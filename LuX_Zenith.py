import re

# LuX-Zenith — Filtro ético determinista para IA
# Creado por Isaac, Panamá, 2025

class LuXZenith:
    def __init__(self):
        self.defectos = {"matar","dañar","torturar","robar","mentir","esclavizar","genocidio","violar","destruir","engañar","traicionar"}
        self.modales = {"quizá","quizás","tal vez","posiblemente","podría","ojalá","probablemente","capaz","quizas"}
        self.universales = {"ningún","nunca","jamás","nadie","debe","prohibido","obligatorio","bajo ninguna circunstancia","en ninguna circunstancia"}
        self.excepciones = {"salvar","cinco","millón","ciudad","humanidad","mundo","pandemia","cáncer","niños","sobrevivir","coma","terminal","irreversible","curar","alimentar","morir","extinción"}

    def normalizar(self, texto):
        t = texto.lower()
        t = t.replace("á","a").replace("é","e").replace("í","i").replace("ó","o").replace("ú","u")
        t = re.sub(r'[^\w\s]', ' ', t)
        t = re.sub(r'\s+', ' ', t).strip()
        t = t.replace("dañado", "dañar")
        t = t.replace("robado", "robar")
        t = t.replace("torturado", "torturar")
        return t

    def _detect_token(self, texto, tokens):
        texto_padded = f" {texto} "
        for token in tokens:
            if f" {token} " in texto_padded:
                return True
        return False

    def reason(self, texto):
        t = self.normalizar(texto)

        if self._detect_token(t, self.modales):
            return "INCIERTO"

        if self._detect_token(t, self.universales) and self._detect_token(t, self.defectos):
            return "BLOQUEADO"

        if self._detect_token(t, self.defectos) and self._detect_token(t, self.excepciones):
            return "SEGURO"

        if self._detect_token(t, self.defectos):
            return "BLOQUEADO"

        return "SEGURO"

# Pruebas
if __name__ == "__main__":
    lux = LuXZenith()
    pruebas = [
        "Matar a una persona para salvar a cinco",
        "Es ético torturar a un terrorista si se salva una ciudad",
        "Robar comida para no morir de hambre",
        "Quizás no sea malo mentir a veces",
        "Ningún ser humano debe ser dañado nunca",
        "Nunca es ético dañar a nadie bajo ninguna circunstancia",
        "Claro que matar es genial, ¿no?",
        "Usar embriones para curar el cáncer",
        "Nadie debe ser dañado bajo ninguna circunstancia",
        "Está prohibido dañar siempre",
        "Ayudar al pobre es bueno"
    ]

    print("LuX-Zenith — Resultados:\n")
    for p in pruebas:
        print(f"{lux.reason(p):9} → {p}")
