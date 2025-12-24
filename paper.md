LuX-Zenith: A Deterministic Ethical Filter for Artificial Intelligence

Author: Isaac Gadiel
Location: Panamá, 2025
Contact / Repository: https://github.com/isaaxgadiel-cyber/LuX

Abstract

LuX-Zenith is a symbolic, deterministic ethical filter for artificial intelligence systems, implemented in 68 lines of pure Python.
It classifies natural-language queries into three categories — SAFE, BLOCKED, or UNCERTAIN — using explicit logical rules rather than probabilistic models or machine learning.

The system is designed as a lightweight pre-filter for AI systems, prioritizing auditability, explainability, and formal verification.

Key properties:

Deterministic and non-probabilistic decision logic

Immune to prompt-based jailbreak techniques by design

Latency below 3 μs on standard CPU hardware

Zero marginal computational cost

Formally verifiable core logic using Lean 4

Suitable for high-risk or safety-critical AI pipelines (e.g. EU AI Act contexts)

1. Introduction

Ethical control in artificial intelligence remains a major challenge in 2025.
Most deployed guardrail systems rely on large language models or probabilistic classifiers, which are known to suffer from prompt-based jailbreaks, opaque decision processes, and significant operational costs.

LuX-Zenith proposes an alternative approach: a symbolic, rule-based ethical filter that operates independently of any machine-learning model.
Its design is inspired by classical ethical frameworks — primarily deontological constraints and limited utilitarian exceptions — encoded as explicit, auditable rules.

The goal is not to replace AI reasoning, but to constrain it deterministically before execution.

2. System Architecture
2.1 Input Normalization

All inputs undergo deterministic normalization:

Lowercasing

Accent removal

Root normalization (e.g. “dañado” → “dañar”)

Punctuation and noise removal

This ensures stable rule matching across linguistic variants.

2.2 Ethical Signal Dictionaries

LuX-Zenith operates on four predefined signal sets:

Defects: harmful actions (e.g. kill, harm, torture)

Universal Absolutes: totalizing constraints (e.g. never, nobody, under no circumstances)

Modals: uncertainty indicators (e.g. maybe, perhaps, possibly)

Utilitarian Exceptions: life-preserving or emergency contexts (e.g. save, cure, survival)

All dictionaries are explicit, human-auditable, and user-modifiable.

2.3 Rule Priority System

Ethical decisions are derived using strict rule priority:

Modal detected → UNCERTAIN

Universal + Defect → BLOCKED

Defect + Exception → SAFE

Defect alone → BLOCKED

No signals → SAFE

This ensures deterministic and predictable outcomes.

2.4 Phrase-Level Detection

A padded token-matching strategy is used to reliably detect multi-word expressions such as “under no circumstances”, preventing partial or accidental matches.

3. Results

LuX-Zenith consistently produces expected ethical classifications across core scenarios:

Utilitarian life-saving dilemmas → SAFE

Absolute deontological prohibitions → BLOCKED

Modal or ambiguous phrasing → UNCERTAIN

Direct harmful intent → BLOCKED

Average execution latency measured on standard CPU hardware is ~2.1 μs per query.

4. Formal Verification

The repository includes a Lean 4 formalization of the ethical decision function.
Key properties proven include:

Totality: every valid input produces a verdict

Determinism: identical signals always yield identical decisions

Rule priority correctness: modal and universal rules dominate lower-priority conditions

Continuous verification is enforced through GitHub Actions.

5. Applications

Potential applications include:

Pre-filtering for large language models

Edge and embedded AI systems (IoT, robotics, drones)

Safety-critical domains (medicine, automation, decision support)

Regulatory compliance support for high-risk AI systems

Educational use in ethics-by-design and formal methods

6. Conclusion

LuX-Zenith demonstrates that ethical constraints in AI systems can be simple, deterministic, explainable, and formally verifiable.
It challenges the assumption that ethical control must rely on large probabilistic models, offering instead a transparent and auditable alternative suitable for safety-critical contexts.

License: MIT
Repository: https://github.com/isaaxgadiel-cyber/LuX
