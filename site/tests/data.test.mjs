import assert from 'node:assert/strict';
import { mkdtemp, mkdir, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { test } from 'node:test';
import { loadExperiments } from '../src/data/experiments.ts';

test('ordered metadata reports available plots and requires safe unique IDs', async () => {
  const root = await mkdtemp(join(tmpdir(), 'gallery-data-'));
  const config = join(root, 'experiments.json');
  const plots = join(root, 'plots');
  const entries = [{ id: 'z_last', title: 'A < B & "quoted"' }, { id: 'a_first', title: 'A long title '.repeat(20) }];
  try {
    await mkdir(plots);
    await writeFile(config, JSON.stringify({ experiments: entries }));
    for (const { id } of entries) {
      for (const ext of ['png', 'svg']) await writeFile(join(plots, `${id}.${ext}`), 'plot');
    }
    const complete = entries.map(entry => ({ ...entry, hasSvg: true, hasPng: true }));
    assert.deepEqual(loadExperiments(config, plots), complete);
    for (const ext of ['svg', 'png']) {
      const path = join(plots, `z_last.${ext}`);
      await rm(path);
      assert.deepEqual(loadExperiments(config, plots), [
        { ...complete[0], [ext === 'svg' ? 'hasSvg' : 'hasPng']: false },
        complete[1],
      ]);
      await writeFile(path, 'plot');
    }
    await rm(plots, { recursive: true });
    assert.deepEqual(loadExperiments(config, plots), entries.map(entry => ({ ...entry, hasSvg: false, hasPng: false })));
    for (const experiments of [
      [{ id: '../outside', title: 'Unsafe' }],
      [{ id: 'space id', title: 'Unsafe' }],
      [entries[0], entries[0]],
      [{ id: 'ok', title: '' }],
      [null],
    ]) {
      await writeFile(config, JSON.stringify({ experiments }));
      assert.throws(() => loadExperiments(config, plots));
    }
    await writeFile(config, '{}');
    assert.throws(() => loadExperiments(config, plots), /experiments/);
    await writeFile(config, '{');
    assert.throws(() => loadExperiments(config, plots), SyntaxError);
  } finally {
    await rm(root, { recursive: true, force: true });
  }
});
