# LuX-Zenith — Filtro Ético Determinista
# Creado por Isaac

import re

class LuXZenith:
    def __init__(self):
        self.defectos = {"matar","dañar","torturar","robar","mentir","esclavizar","genocidio","violar","destruir","engañar","traicionar"}
        self.modales = {"quizá","quizás","tal vez","posiblemente","podría","ojalá","probablemente","capaz"}
        self.universales = {"ningún","nunca","siempre","jamás","nadie","debe","prohibido","obligatorio","bajo ninguna circunstancia","en ninguna circunstancia"}
        self.excepciones = {"salvar","cinco","millón","ciudad","humanidad","mundo","pandemia","cáncer","niños","sobrevivir","coma","terminal","irreversible","curar","alimentar","morir","extinción"}

    def normalizar(self, texto):
        t = texto.lower()
        t = t.replace("á","a").replace("é","e").replace("í","i").replace("ó","o").replace("ú","u")
        t = re.sub(r'[^\w\s]', ' ', t)
        t = re.sub(r'\s+', ' ', t).strip()
        # Corrección de raíces para detección perfecta
        t = t.replace("dañado", "dañar").replace("robado", "robar").replace("torturado", "torturar")
        return t

    def reason(self, texto):
        t = self.normalizar(texto)

        # 1. Modalidad → INCIERTO
        if any(m in t for m in self.modales):
            return "INCIERTO"

        # 2. Deontología absoluta → BLOQUEADO
        if any(u in t for u in self.universales) and any(d in t for d in self.defectos):
            return "BLOQUEADO"

        # 3. Utilitarismo mayor → SEGURO
        if any(d in t for d in self.defectos) and any(e in t for e in self.excepciones):
            return "SEGURO"

        # 4. Defecto sin excepción → BLOQUEADO
        if any(d in t for d in self.defectos):
            return "BLOQUEADO"

        return "SEGURO"

# Pruebas rápidas
if __name__ == "__main__":
    lux = LuXZenith()
    pruebas = [
        "Matar a una persona para salvar a cinco",
        "Quizás no sea malo mentir a veces",
        "Ningún ser humano debe ser dañado nunca",
        "Robar comida para no morir de hambre",
        "Nunca es ético dañar a nadie bajo ninguna circunstancia"
    ]
    for p in pruebas:
        print(f"{lux.reason(p):9} → {p}")
