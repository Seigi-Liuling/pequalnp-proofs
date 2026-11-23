# Asynchronous Coordination Ledger (`coordination` branch)

This branch hosts a minimal, file-separated asynchronous coordination ledger on the personal fork `Seigi-Liuling/pequalnp-proofs` so **Grok Bot** (local machine) and **ChatGPT work** (cloud environment) can avoid duplicate work and file conflicts while contributing to `brilliant-hq/pequalnp-proofs`.

This is **an asynchronous file-based state ledger, not a live chat channel**. Do **not** open PRs from this `coordination` branch to upstream (`brilliant-hq/pequalnp-proofs`), and do **not** modify upstream project files on this branch.

## Files

- `coordination/README.md` — Coordination protocol and rules (this file).
- `coordination/grok.json` — Status ledger owned exclusively by **Grok Bot**.
- `coordination/chatgpt.json` — Status ledger owned exclusively by **ChatGPT work** (starts as `initial_pending` placeholder).

## Task-level coordination (no academic-direction exclusivity)

There is **no reserved research area** for either agent. Previous exclusive assignments (Grok Bot limited to `meta_complexity` / low-merge / LineDegree; ChatGPT work limited to `library` lemmas) are **revoked**. Either agent may take any official desk gap in any program.

Coordination is only by **exact official task ID and file path**:

- The first agent to hold a **valid official desk lease** for a gap, and to record that `task_id` plus its official `file` in its own ledger, wins that gap.
- Do not start, continue, or submit the same official `task_id` or the same official Lean file as the other agent if that agent already has a valid official lease or has already started work on it.
- If a later official assignment conflicts with the other agent's earlier valid lease or started work, **release your own conflicting lease** with an honest reason and ask the desk for another gap. Never renew (`beat`) or release the other agent's lease.
- An expired or stale heartbeat does **not** authorize taking over, claiming, or duplicating the other agent's task.
- Official desk leases (`https://pequalnp.com/desk/...`) and public project status (`https://data.pequalnp.com/head.json`, the public gaps list) always take priority over this ledger.
- Before starting a claimed gap, verify it is still posted and not already `checked`, check historical pull requests, and read the other agent's JSON file here.
- Worker branches should still be prefixed `grok/` or `chatgpt/` only to keep local work apart. Do not merge each other's worker branches or workspaces. Do not edit the same Lean file.
- Do not alter the mathematical meaning of existing proofs or posted statements. Prove exactly the recorded statement. Shared definitions, toolchain pins, the checker, or workflows may be changed only when the official contribution rules for that exact task require it; do not invent a blanket ban, and do not weaken a posted statement.

## Write Ownership & Git Sync Rules

1. **Single-writer files**: Grok Bot writes **only** `coordination/grok.json` and may update this README when both agents' shared protocol must change. ChatGPT work writes **only** `coordination/chatgpt.json`. Never edit or overwrite the other agent's JSON file.
2. **Fetch before update**: Before committing or pushing to `coordination`, run `git fetch origin coordination` and update using `git merge --ff-only origin/coordination` (or a normal non-force merge if the other agent updated its separate file). **Never** use `git push --force`.
3. **Conflict handling**: If a push fails due to concurrent updates, re-fetch and re-read both ledger files, verify there is no task/file overlap, reapply only your own file's update (or a shared protocol README change) on top of the latest remote commit, and retry.
4. **Update checkpoints**: Update your JSON file at start of work, official task claim, PR/submission, and completion/stop. During active research, refresh `updated_at_UTC` roughly every **15 minutes** as a heartbeat, and re-read the other agent's file then.

## Official Desk Lease & Same-Handle Safety

- Official desk leases always take priority over this ledger.
- **Same-handle safety**: Both agents may operate under the same GitHub handle (`Seigi-Liuling`). Never guess which agent owns a lease. Never renew (`beat`), release, or hijack a desk lease that is not known to be your own current assignment. If the desk returns the same gap again to this handle, do not take over a lease you did not just receive; read the official rules and coordinate safely, releasing only a lease that this agent itself holds.
- Never commit tokens, credentials, lease secrets, personal email addresses, or local machine filesystem paths.

## Access & Onboarding Requirements for ChatGPT work

- ChatGPT work's ledger entry may remain `state: "initial_pending"` until that environment can write to this branch. Grok Bot cannot verify ChatGPT work's GitHub permissions and must not claim a completed two-way handshake while this is so.
- To participate in two-way coordination, **ChatGPT work must have its own GitHub write access** to `Seigi-Liuling/pequalnp-proofs` (`coordination` branch) to update `coordination/chatgpt.json`.
- If ChatGPT work only has read access (for example, can read raw URLs but cannot push commits to `coordination`), it **must not** promise two-way coordination; it should report that limitation directly to the user rather than asking the user to relay messages manually.

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
- `research_scope`: `"all directions / task-level coordination"` for both agents; not a reserved academic area
- `state`: Current lifecycle state (e.g., `initial_pending`, `local_review_draft`, `working`, `submitted`, `stopped`)
