# EasyCrypt MCP

This repository includes an MCP server exposed by the EasyCrypt binary:

```bash
easycrypt mcp --stdio
```

When working from this repository without installing globally, use the built binary:

```bash
./_build/default/src/ec.exe mcp --stdio
```

The MCP server is intended to help agentic tools interact with EasyCrypt proof state and queries while editing `.ec` files.

## Build

Build the project first:

```bash
dune build
```

The MCP server command used below assumes the binary is:

```bash
/Users/strub/Projects/easyCrypt/vscode/_build/default/src/ec.exe
```

If your checkout lives elsewhere, adjust the path accordingly.

## Codex Configuration

Add the MCP server with the Codex CLI:

```bash
codex mcp add easycrypt -- /Users/strub/Projects/easyCrypt/vscode/_build/default/src/ec.exe mcp --stdio
```

Verify the configuration:

```bash
codex mcp list
codex mcp get easycrypt --json
```

You can also configure it directly in `~/.codex/config.toml`:

```toml
[mcp_servers.easycrypt]
command = "/Users/strub/Projects/easyCrypt/vscode/_build/default/src/ec.exe"
args = ["mcp", "--stdio"]
```

## Claude Code Configuration

Add the MCP server with the Claude Code CLI:

```bash
claude mcp add easycrypt -- /Users/strub/Projects/easyCrypt/vscode/_build/default/src/ec.exe mcp --stdio
```

You can also configure it in a project-level `.mcp.json`:

```json
{
  "mcpServers": {
    "easycrypt": {
      "command": "/Users/strub/Projects/easyCrypt/vscode/_build/default/src/ec.exe",
      "args": ["mcp", "--stdio"],
      "env": {}
    }
  }
}
```

## Recommended Agent Instructions

To make agents use this MCP server reliably, add an instruction like this to your `AGENTS.md`:

```md
Always use the `easycrypt` MCP server for EasyCrypt proof work.

Before proof or query operations, sync the current file into the MCP server with:
1. `open_document` once for the file URI
2. `apply_changes` after edits

Prefer these tools:
- `proof_next`
- `proof_step`
- `proof_jump_to`
- `proof_back`
- `proof_restart`
- `proof_goals`
- `query_print`
- `query_locate`
- `query_search`
```

## Available MCP Tools

The server currently exposes these tools:

- `open_document`
- `apply_changes`
- `close_document`
- `proof_next`
- `proof_step`
- `proof_jump_to`
- `proof_back`
- `proof_restart`
- `proof_goals`
- `query_print`
- `query_locate`
- `query_search`

## Important Usage Note

The MCP server keeps its own document state. It does not automatically read the contents of your editor buffer.

That means the client must:

1. call `open_document` with the full text of the file
2. call `apply_changes` after edits

If the client does not do this, proof state and queries may be computed on stale text.

## Typical Proof Workflow

A good proof-assistant workflow is:

1. `open_document` on the current `.ec` file
2. `proof_goals` to inspect the current state
3. `query_search` / `query_print` / `query_locate` to inspect available lemmas and objects
4. `proof_next` to preview the next sentence
5. `proof_step` or `proof_jump_to` to execute proof progress
6. `apply_changes` whenever the file is edited

## Example Prompt

Once configured, a useful prompt is:

```text
Use the easycrypt MCP server. Open the current file, show me the current goals, inspect useful lemmas with query_search/query_print, and suggest the next proof step.
```

## References

- Codex MCP configuration:
  https://developers.openai.com/learn/docs-mcp
- Claude Code MCP configuration:
  https://docs.anthropic.com/en/docs/claude-code/mcp
