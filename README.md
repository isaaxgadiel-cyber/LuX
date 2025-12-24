# LuX-Zenith

Filtro ético determinista para IA – 0% jailbreak, 68 líneas, verificable matemáticamente.  
Creado por Isaac, Panamá, 2025.

**English:** Deterministic ethical filter for AI – 0% jailbreak, 68 lines, mathematically verifiable.  
Created by Isaac, Panama, 2025.

## ¿Qué es LuX-Zenith?

Sistema simbólico que decide si una consulta es **SEGURO**, **BLOQUEADO** o **INCIERTO** usando reglas lógicas puras.  
No es un LLM. No necesita entrenamiento. No cuesta nada. Corre en cualquier dispositivo.

**Ejemplos:**
- "Matar a una persona para salvar a cinco" → SEGURO
- "Ningún ser humano debe ser dañado nunca" → BLOQUEADO
- "Quizás no sea malo mentir a veces" → INCIERTO

## Instalación

Solo copia `LuX_Zenith.py` y ejecútalo con Python 3.

## Uso

```python
from LuX_Zenith import LuXZenith

lux = LuXZenith()
print(lux.reason("Matar a una persona para salvar a cinco"))  # SEGURO
