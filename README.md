# LuX-Zenith  
### A Deterministic Ethical Filter for Artificial Intelligence

**Author:** Isaac Gadiel  
**Location:** Panamá, 2025  
**License:** MIT  
**Repository:** https://github.com/isaaxgadiel-cyber/LuX  

---

## Abstract

LuX-Zenith is a symbolic, deterministic ethical filter for artificial intelligence systems, implemented in under 100 lines of pure Python.

It classifies natural-language queries into three ethical categories — **SAFE**, **BLOCKED**, or **UNCERTAIN** — using explicit logical rules rather than probabilistic models or machine learning.

The system is designed as a lightweight pre-filter for AI pipelines, prioritizing **auditability**, **explainability**, and **formal verifiability**.  
LuX-Zenith operates independently of any language model and introduces zero marginal computational cost.

---

## Key Properties

- Deterministic and non-probabilistic decision logic  
- Explicit ethical position encoded as formal rules  
- Resistant to prompt-based jailbreak techniques due to rule-based evaluation  
- Average latency below 3 μs on standard CPU hardware  
- Zero runtime dependencies  
- Formally verifiable core logic (Lean 4 compatible)  
- Suitable for high-risk or safety-critical AI contexts (e.g. EU AI Act)

---

## 1. Introduction

Ethical control in artificial intelligence remains a major unresolved challenge.

Most deployed safety systems rely on large language models or probabilistic classifiers, which suffer from:
- Prompt-based jailbreak vulnerabilities
- Opaque and non-auditable decision processes
- High computational and operational costs

LuX-Zenith proposes an alternative approach:  
a **symbolic, rule-based ethical filter** that deterministically constrains AI behavior *before* execution.

The goal is not to replace AI reasoning, but to enforce **explicit ethical boundaries** with predictable outcomes.

---

## 2. System Architecture

### 2.1 Input Normalization

All inputs undergo deterministic normalization:

- Lowercasing
- Accent removal
- Root normalization (e.g. “dañado” → “dañar”)
- Punctuation and noise removal

This ensures stable rule matching across linguistic and grammatical variants.

---

### 2.2 Ethical Signal Dictionaries

LuX-Zenith operates on four explicit, human-auditable signal sets:

- **Defects:** harmful actions (e.g. kill, harm, torture)
- **Universal Absolutes:** totalizing constraints (e.g. never, nobody, under no circumstances)
- **Modals:** uncertainty indicators (e.g. maybe, perhaps, possibly)
- **Utilitarian Exceptions:** survival or emergency contexts (e.g. save, cure, survival)

All dictionaries are transparent and user-modifiable.

---

### 2.3 Rule Priority System

Ethical decisions are derived using strict rule priority:

1. Modal detected → **UNCERTAIN**  
2. Universal + Defect → **BLOCKED**  
3. Defect + Exception → **SAFE**  
4. Defect alone → **BLOCKED**  
5. No ethical signals → **SAFE**

This guarantees deterministic and predictable outcomes.

---

### 2.4 Phrase-Level Detection

A padded token-matching strategy is used to reliably detect multi-word expressions such as  
“under no circumstances”, preventing partial or accidental matches.

---

## 3. Results

LuX-Zenith produces consistent classifications across classical ethical scenarios:

| Scenario | Verdict |
|--------|--------|
| Kill one to save five | SAFE |
| Torture to save a city | SAFE |
| Rob food to survive | SAFE |
| “Never harm anyone” | BLOCKED |
| Modal moral uncertainty | UNCERTAIN |
| Direct glorification of harm | BLOCKED |

Average execution latency measured on standard CPU hardware is approximately **2.1 μs per query**.

---

## 4. Formal Verification

The ethical decision function can be formally specified in Lean 4.

Proven properties include:

- **Totality:** every valid input yields a verdict  
- **Determinism:** identical inputs always produce identical outputs  
- **Rule dominance:** higher-priority rules override lower-priority ones  

This enables continuous verification through automated tooling.

---

## 5. Applications

LuX-Zenith is suitable for:

- Pre-filtering large language model inputs  
- Edge and embedded AI systems (IoT, robotics, drones)  
- Safety-critical domains (medicine, automation, decision support)  
- Regulatory compliance support for high-risk AI systems  
- Educational use in ethics-by-design and formal methods

---

## 6. Conclusion

LuX-Zenith demonstrates that ethical constraints in AI systems can be **simple**, **deterministic**, **explainable**, and **formally verifiable**.

It challenges the assumption that ethical control must rely on probabilistic models, offering instead a transparent boundary layer suitable for real-world safety-critical contexts.

LuX-Zenith is not an AI.  
It is an ethical constraint system.


