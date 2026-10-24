import { readFileSync, statSync } from 'node:fs';
import { resolve } from 'node:path';

export type Experiment = { id: string; title: string; disable_reason?: string; hasSvg: boolean; hasPng: boolean };

export function loadExperiments(
  configFile = process.env.EXPERIMENTS_FILE || resolve('../experiments.json'),
  plotsDir = resolve('public/plots'),
): Experiment[] {
  const config = JSON.parse(readFileSync(configFile, 'utf8'));
  if (!config || !Array.isArray(config.experiments)) {
    throw new Error('Expected an experiments array in experiments.json');
  }
  const seen = new Set<string>();
  return config.experiments.map((entry: unknown) => {
    const { id, title, disable_reason } = (entry ?? {}) as Partial<Experiment>;
    if (typeof id !== 'string' || !/^[A-Za-z0-9_-]+$/.test(id)) {
      throw new Error(`Invalid experiment id: ${id}`);
    }
    if (seen.has(id)) throw new Error(`Duplicate experiment id: ${id}`);
    seen.add(id);
    if (typeof title !== 'string' || !title.trim()) {
      throw new Error(`Missing title for experiment: ${id}`);
    }
    if (Object.hasOwn(entry as object, 'disable_reason') &&
        (typeof disable_reason !== 'string' || !disable_reason.trim())) {
      throw new Error(`Invalid disable_reason for experiment: ${id}`);
    }
    return {
      ...(disable_reason === undefined ? {} : { disable_reason }),
      id,
      title,
      hasSvg: statSync(resolve(plotsDir, `${id}.svg`), { throwIfNoEntry: false })?.isFile() ?? false,
      hasPng: statSync(resolve(plotsDir, `${id}.png`), { throwIfNoEntry: false })?.isFile() ?? false,
    };
  });
}
