// QUICK-BUNDLE — quarantined dirty-bundling shim.
//
// Beta-1 ships a "bundled" .vsix that includes pre-built `ec` and
// `ecd` binaries under <extension>/bin/<platform>/. The proper
// implementation (build-script in scripts/, full discovery chain
// matching BETA.md, multi-platform support, CI hook) is documented
// in HANDOFF-VSCODE-FIRST.md § G as a ~1 day follow-up.
//
// Until that lands, this module is the entirety of the bundling
// integration on the VSCode side: a tiny helper that returns the
// absolute path to a bundled binary if one exists. Callers in
// extension.ts plug it in as the LAST entry of the binary
// discovery chain — after env vars and settings — so a configured
// path or env var still wins.
//
// To clean up: delete this file, delete vscode/scripts/quick-bundle*,
// remove the two `quickBundleBinary(...)` calls from extension.ts,
// and replace with the proper resolver chain.
//
// Companion script: vscode/scripts/quick-bundle.sh.

import * as fs from 'fs';
import * as path from 'path';

function platformDir(): string | undefined {
  if (process.platform === 'darwin' && process.arch === 'arm64') return 'darwin-arm64';
  // Other targets land with the proper bundling work.
  return undefined;
}

export function quickBundleBinary(
  name: 'ec' | 'ecd',
  extensionPath: string,
): string | undefined {
  const platform = platformDir();
  if (!platform) return undefined;
  const filename = name === 'ec' ? 'ec.native' : 'ecd.native';
  const candidate = path.join(extensionPath, 'bin', platform, filename);
  try {
    fs.accessSync(candidate, fs.constants.X_OK);
    return candidate;
  } catch {
    return undefined;
  }
}
