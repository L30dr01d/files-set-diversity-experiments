import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { cp, mkdtemp, mkdir, readFile, rm, stat, symlink, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { test } from 'node:test';

const site = fileURLToPath(new URL('../', import.meta.url));
const entries = [
  { id: 'z_last', title: 'A < B & "quoted"' },
  { id: 'a_first', title: 'An experiment with a long title '.repeat(10) },
];
const svg = '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1200 200"><text x="20" y="100">Plot</text></svg>';
const png = Buffer.from('iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO+aD1sAAAAASUVORK5CYII=', 'base64');

function elements(html, tag) {
  return [...html.matchAll(/<([a-z][\w-]*)\b((?:"[^"]*"|'[^']*'|[^'">])*)>/gi)]
    .filter(([, name]) => name === tag).map(([, , text]) =>
    Object.fromEntries([...text.matchAll(/([\w:-]+)(?:="([^"]*)"|='([^']*)'|=([^\s>]+))?/g)]
      .map(([, name, double, single, bare]) => [name, double ?? single ?? bare ?? ''])));
}

test('Astro builds an SVG gallery, full plot pages, and downloads at root and repository paths', async () => {
  const root = await mkdtemp(join(tmpdir(), 'gallery-build-'));
  try {
    await cp(join(site, 'src'), join(root, 'src'), { recursive: true });
    for (const file of ['package.json', 'astro.config.mjs']) await cp(join(site, file), join(root, file));
    await symlink(join(site, 'node_modules'), join(root, 'node_modules'), 'dir');
    await mkdir(join(root, 'public', 'plots'), { recursive: true });
    const metadata = join(root, 'experiments.json');
    await writeFile(metadata, JSON.stringify({ experiments: entries }));
    for (const { id } of entries) {
      await writeFile(join(root, 'public', 'plots', `${id}.svg`), svg);
      await writeFile(join(root, 'public', 'plots', `${id}.png`), png);
    }
    const build = (base) => spawnSync(process.execPath, [join(site, 'node_modules', 'astro', 'bin', 'astro.mjs'), 'build'], {
      cwd: root,
      env: { ...process.env, ASTRO_TELEMETRY_DISABLED: '1', EXPERIMENTS_FILE: metadata, BASE_PATH: base, SITE_URL: 'https://example.github.io' },
      encoding: 'utf8',
      timeout: 120_000,
    });
    for (const base of ['/', '/ci-experiments/']) {
      const result = build(base);
      assert.equal(result.status, 0, result.stdout + result.stderr);
      const index = await readFile(join(root, 'dist', 'index.html'), 'utf8');
      assert.match(index, /<h1\b[^>]*>Text Set Diversity Experiments<\/h1>/);
      assert.match(index, /<h2\b[^>]*>A &lt; B &amp; /);
      assert.ok(index.indexOf('z_last.svg') < index.indexOf('a_first.svg'));
      assert.equal(elements(index, 'img').length, 2);
      assert.ok(elements(index, 'img').every(img => img.loading === 'lazy' && img.alt));
      const pages = [index];
      for (const { id } of entries) {
        const detail = await readFile(join(root, 'dist', 'experiments', id, 'index.html'), 'utf8');
        const links = elements(detail, 'a');
        assert.ok(links.some(link => link.href === base));
        for (const ext of ['png', 'svg']) {
          assert.ok(links.some(link => link.href === `${base}plots/${id}.${ext}` && 'download' in link));
          const original = await readFile(join(root, 'dist', 'plots', `${id}.${ext}`));
          assert.deepEqual(original, ext === 'png' ? png : Buffer.from(svg));
        }
        assert.equal(elements(detail, 'img').length, 1);
        assert.equal(links.filter(link => 'download' in link).length, 2);
        pages.push(detail);
      }
      for (const html of pages) {
        assert.equal(elements(html, 'html')[0]['data-theme'], 'light');
        assert.ok(elements(html, 'meta').some(meta => meta.name === 'color-scheme' && meta.content === 'light'));
        assert.equal(elements(html, 'script').length, 0);
        assert.ok(elements(html, 'img').every(img => img.src.endsWith('.svg') && img.alt));
        assert.ok(elements(html, 'link').some(link => link.rel === 'stylesheet' && link.href.startsWith(`${base}_astro/`)));
        for (const { href, src } of [...elements(html, 'a'), ...elements(html, 'img'), ...elements(html, 'link')]) {
          const url = href ?? src;
          if (!url || url.startsWith('#')) continue;
          assert.ok(url.startsWith(base), `URL outside base: ${url}`);
          const relative = url.slice(base.length);
          const target = join(root, 'dist', relative, ...(url.endsWith('/') ? ['index.html'] : []));
          assert.ok((await stat(target)).isFile(), url);
        }
      }
    }
    for (const missing of [['svg'], ['png'], ['svg', 'png']]) {
      for (const ext of missing) await rm(join(root, 'public', 'plots', `z_last.${ext}`));
      for (const base of ['/', '/ci-experiments/']) {
        const result = build(base);
        assert.equal(result.status, 0, result.stdout + result.stderr);
        const index = await readFile(join(root, 'dist', 'index.html'), 'utf8');
        assert.equal(elements(index, 'a').filter(link => link.href?.startsWith(`${base}experiments/`)).length, 2);
        assert.equal(elements(index, 'img').length, missing.includes('svg') ? 1 : 2);
        assert.equal(index.includes('SVG preview unavailable'), missing.includes('svg'));
        const detail = await readFile(join(root, 'dist', 'experiments', 'z_last', 'index.html'), 'utf8');
        assert.equal(elements(detail, 'img').length, missing.includes('svg') ? 0 : 1);
        assert.equal(detail.includes('Plot .svg was not found.'), missing.includes('svg'));
        const links = elements(detail, 'a');
        assert.ok(links.some(link => link.href === base));
        for (const ext of ['png', 'svg']) {
          assert.equal(links.some(link => link.href === `${base}plots/z_last.${ext}` && 'download' in link), !missing.includes(ext));
        }
        assert.equal(elements(detail, 'button').filter(button => 'disabled' in button).length, missing.length);
      }
      for (const ext of missing) await writeFile(join(root, 'public', 'plots', `z_last.${ext}`), ext === 'png' ? png : svg);
    }
    for (const stale of [true, false]) {
      await writeFile(metadata, JSON.stringify({ experiments: [{ ...entries[0], disable_reason: 'Paused <script>alert(1)</script> & slow' }] }));
      if (!stale) {
        for (const ext of ['svg', 'png']) await rm(join(root, 'public', 'plots', `z_last.${ext}`));
      }
      const result = build('/');
      assert.equal(result.status, 0, result.stdout + result.stderr);
      for (const file of ['index.html', 'experiments/z_last/index.html']) {
        const html = await readFile(join(root, 'dist', file), 'utf8');
        assert.match(html, /Paused &lt;script&gt;alert\(1\)&lt;\/script&gt; &amp; slow/);
        assert.equal(elements(html, 'img').length, 0);
        assert.equal(elements(html, 'script').length, 0);
        assert.equal(elements(html, 'a').filter(link => 'download' in link).length, 0);
        assert.ok(!html.includes('SVG preview unavailable') && !html.includes('Plot .svg was not found.'));
      }
    }
    await writeFile(metadata, JSON.stringify({ experiments: [{ id: '../outside', title: 'Unsafe' }] }));
    const unsafe = build('/');
    assert.notEqual(unsafe.status, 0);
    assert.match(unsafe.stdout + unsafe.stderr, /Invalid experiment id/);
  } finally {
    await rm(root, { recursive: true, force: true });
  }
});
