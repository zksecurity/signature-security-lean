---
name: Security proof review
about: Review a lazy signature security statement, model, or proof
title: "[Review] "
---

## Scope

- Commit:
- Endpoint: BLS/co-CDH, BLS/lazy AGM, OOPS/lazy AGM, or Proximity/lazy AGM
- Paper/version and statement being compared:
- Review guide: https://github.com/zksecurity/signature-security-lean/blob/main/docs/review-guide.md

## Checklist

- [ ] Match the adversary and winning event to the intended claim.
- [ ] Check adaptivity, stopping, and final target selection.
- [ ] Check shared-cache, transcript, freshness, and visible-token accounting.
- [ ] Check both DLog branches and the collision term.
- [ ] Check the OOPS degree rule or Proximity noncollision premise.
- [ ] Confirm finite-domain, random-oracle, and computational-cost limits.
- [ ] For generic hardness, check every named solver certificate; for concrete-machine hardness,
  check the source certificate and derived target budgets, including both AGM branches.
- [ ] Record build evidence and axiom footprints for this commit.

## Findings

For each finding, include source permalinks, the expected paper statement, the actual
formal statement or behavior, and the impact. Distinguish model mismatches from proof gaps.

## Verification

- Build result and log/run link:
- Axiom checks:
- Tests examined:
- Remaining questions:
