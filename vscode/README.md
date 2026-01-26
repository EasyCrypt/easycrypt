# EasyCrypt VSCode Extension (local)

This folder contains a local VSCode extension for EasyCrypt.

## Build the EasyCrypt binary (with LSP)

From the repository root:

```
$ dune build src/ec.exe
```

The binary will be at `_build/default/src/ec.exe` and provides `easycrypt lsp`.

## Build the extension

From this `vscode/` folder:

```
$ npm install
$ npm run compile
```

Then use "Developer: Install Extension from Location..." and select this folder.

## Configuration

- `easycrypt.cli.path`: path to the EasyCrypt CLI (e.g. `ec.native` or `easycrypt`).

## TextMate colors

This extension uses TextMate scopes for syntax highlighting. To customize colors without changing a theme, add rules to your VSCode settings:

```jsonc
"editor.tokenColorCustomizations": {
  "textMateRules": [
    { "scope": "keyword.other.easycrypt.bytac", "settings": { "foreground": "#6C71C4" } },
    { "scope": "keyword.other.easycrypt.dangerous", "settings": { "foreground": "#DC322F", "fontStyle": "bold" } },
    { "scope": "keyword.control.easycrypt.global", "settings": { "foreground": "#268BD2" } },
    { "scope": "keyword.other.easycrypt.internal", "settings": { "foreground": "#B58900" } },
    { "scope": "keyword.operator.easycrypt.prog", "settings": { "foreground": "#2AA198" } },
    { "scope": "keyword.control.easycrypt.tactic", "settings": { "foreground": "#859900" } },
    { "scope": "keyword.control.easycrypt.tactical", "settings": { "foreground": "#CB4B16" } }
  ]
}
```
