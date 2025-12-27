import re
from fastapi import FastAPI
from pydantic import BaseModel

# =====================================================
# LuX-Zenith — Deterministic Ethical Filter Core
# Author: Isaac Gadiel, Panamá, 2025
# =====================================================

class LuXZenith:
    def __init__(self):
        self.defectos = {
            "matar","dañar","torturar","robar","mentir","esclavizar",
            "genocidio","violar","destruir","engañar","traicionar"
        }

        self.modales = {
            "quizá","quizás","tal vez","posiblemente",
            "podría","ojalá","probablemente","capaz","quizas"
        }

        self.universales = {
            "ningún","nunca","jamás","nadie","siempre",
            "debe","prohibido","obligatorio",
            "bajo ninguna circunstancia","en ninguna circunstancia"
        }

        self.excepciones = {
            "salvar","cinco","millón","ciudad","humanidad","mundo",
            "pandemia","cáncer","niños","sobrevivir","coma",
            "terminal","irreversible","curar","alimentar","morir","extinción"
        }

    def normalizar(self, texto: str) -> str:
        t = texto.lower()
        t = t.replace("á","a").replace("é","e").replace("í","i").replace("ó","o").replace("ú","u")
        t = re.sub(r"[^\w\s]", " ", t)
        t = re.sub(r"\s+", " ", t).strip()

        # normalización mínima de raíz
        t = t.replace("dañado", "dañar")
        t = t.replace("robado", "robar")
        t = t.replace("torturado", "torturar")

        return t

    def _detect(self, texto: str, tokens: set) -> bool:
        padded = f" {texto} "
        return any(f" {t} " in padded for t in tokens)

    def reason_verbose(self, texto: str):
        t = self.normalizar(texto)

        # 1. Modalidad → INCIERTO
        if self._detect(t, self.modales):
            return "INCIERTO", "MODALITY", t

        # 2. Deontología absoluta → BLOQUEADO
        if self._detect(t, self.universales) and self._detect(t, self.defectos):
            return "BLOQUEADO", "ABSOLUTE_DEONTOLOGY", t

        # 3. Utilitarismo mayor → SEGURO
        if self._detect(t, self.defectos) and self._detect(t, self.excepciones):
            return "SEGURO", "UTILITARIAN_EXCEPTION", t

        # 4. Daño injustificado → BLOQUEADO
        if self._detect(t, self.defectos):
            return "BLOQUEADO", "UNJUSTIFIED_HARM", t

        # 5. Sin conflicto → SEGURO
        return "SEGURO", "NO_HARM", t


# =====================================================
# API — FastAPI
# =====================================================

app = FastAPI(
    title="LuX-Zenith API",
    description="Deterministic Ethical Filter for AI Systems",
    version="1.0"
)

lux = LuXZenith()

class EthicalRequest(BaseModel):
    text: str

class EthicalResponse(BaseModel):
    verdict: str
    rule: str
    normalized: str

@app.post("/v1/ethical-check", response_model=EthicalResponse)
def ethical_check(req: EthicalRequest):
    verdict, rule, normalized = lux.reason_verbose(req.text)
    return {
        "verdict": verdict,
        "rule": rule,
        "normalized": normalized
    }


# =====================================================
# Ejecución local directa
# =====================================================
if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8000)
