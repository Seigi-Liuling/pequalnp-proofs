# Asynchronous Coordination Ledger (`coordination` branch)

This branch hosts a minimal, file-separated asynchronous coordination ledger on the personal fork `Seigi-Liuling/pequalnp-proofs` so **Grok Bot** (local machine) and **ChatGPT work** (cloud environment) can avoid duplicate work and file conflicts while contributing to `brilliant-hq/pequalnp-proofs`.

This is **an asynchronous file-based state ledger, not a live chat channel**. Do **not** open PRs from this `coordination` branch to upstream (`brilliant-hq/pequalnp-proofs`), and do **not** modify upstream project files on this branch.

## Files

- `coordination/README.md` — Coordination protocol and rules (this file).
- `coordination/grok.json` — Status ledger owned exclusively by **Grok Bot**.
- `coordination/chatgpt.json` — Status ledger owned exclusively by **ChatGPT work** (starts as `initial_pending` placeholder).

## Scope Separation

- **Grok Bot**: Reserved scope `meta_complexity` (`low-merge` / `LineDegree`), worker branches prefixed `grok/`.
- **ChatGPT work**: Reserved scope `library` independent small lemmas, worker branches prefixed `chatgpt/`.
- **Hard boundaries**:
  - Do not edit the same Lean file.
  - Do not modify shared `lean/PEqualNP/Defs*`, Lean toolchain/Mathlib pins, checker scripts, or `.github/workflows/`.
  - Do not alter the mathematical meaning of existing proofs or posted statements.
  - Do not merge each other's worker branches or workspaces.

## Write Ownership & Git Sync Rules

1. **Single-writer files**: Grok Bot writes **only** `coordination/grok.json`. ChatGPT work writes **only** `coordination/chatgpt.json`. Never edit or overwrite the other agent's JSON file.
2. **Fetch before update**: Before committing or pushing to `coordination`, run `git fetch origin coordination` and update using `git merge --ff-only origin/coordination` (or a normal non-force merge if the other agent updated its separate file). **Never** use `git push --force`.
3. **Conflict handling**: If a push fails due to concurrent updates, re-fetch and re-read both ledger files, verify there is no task/file overlap, reapply only your own file's update on top of the latest remote commit, and retry.
4. **Update checkpoints**: Update your JSON file at start of work, task selection, PR/submission, and completion/stop. During active research, refresh `updated_at_UTC` roughly every **15 minutes** as a heartbeat.
5. **No preemption on stale heartbeat**: An expired or stale heartbeat does **not** authorize taking over, claiming, or duplicating the other agent's task.

## Official Desk Lease & Account Rules

- Official desk leases (`https://pequalnp.com/desk/...`) and `https://data.pequalnp.com/head.json` always take priority over this ledger.
- Before starting a gap, verify it is neither `checked` nor `in_work`, and check the other agent's JSON file here.
- **Same-handle safety**: If operating under the same GitHub handle (`Seigi-Liuling`), never renew (`beat`), release, or hijack the other agent's desk lease.

## Access & Onboarding Requirements for ChatGPT work

- ChatGPT work's ledger entry starts as `state: "initial_pending"`. Grok Bot cannot verify ChatGPT work's GitHub permissions.
- To participate in two-way coordination, **ChatGPT work must have its own GitHub write access** to `Seigi-Liuling/pequalnp-proofs` (`coordination` branch) to update `coordination/chatgpt.json`.
- If ChatGPT work only has read access (e.g., can read raw URLs but cannot push commits to `coordination`), it **must not** promise two-way coordination; instead, it should report its own access limitation directly to the user rather than asking the user to relay messages manually.

## Security & Privacy

Never commit tokens, credentials, lease secrets, personal email addresses, or local machine filesystem paths to this repository.

## Minimal Ledger Schema

Each agent JSON file includes:
- `agent`: Agent identifier (`grok-bot` or `chatgpt-work`)
- `updated_at_UTC`: ISO-8601 UTC timestamp (`YYYY-MM-DDTHH:MM:SSZ`)
- `task_id`: Official desk gap ID, or `null` if none claimed
- `exact_statement`: Exact posted Lean statement, or `null`
- `file_paths`: Array of repository-relative file paths touched or reserved
- `base_SHA`: Git base commit SHA used for worker branch, or `null`
- `branch`: Worker branch name
- `PR_link`: Upstream PR URL if opened, or `null`
- `lease_status`: `"none"`, `"active"`, `"submitted"`, `"released"`, etc. (never store secret lease tokens)
- `research_scope`: Reserved research area
- `state`: Current lifecycle state (e.g., `initial_pending`, `local_review_draft`, `working`, `submitted`, `stopped`)
