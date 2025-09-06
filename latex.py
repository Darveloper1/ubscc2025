# app.py
from flask import Flask, request, jsonify
import re, math, json

app = Flask(__name__)

ALLOWED = {
    "max": max, "min": min, "abs": abs,
    "log": math.log, "ln": math.log, "exp": math.exp,
    "sqrt": math.sqrt, "pi": math.pi, "e": math.e,
}

def latex_to_python(s: str) -> str:
    s = s.strip()
    # strip $ $, \( \), \left \right and spaces
    s = s.replace("$$", "").replace("$", "").replace(r"\(", "").replace(r"\)", "")
    s = s.replace(r"\left", "").replace(r"\right", "")
    # keep only RHS if there's an equals
    if "=" in s:
        s = s.split("=", 1)[1]

    # \text{Var} -> Var
    s = re.sub(r"\\text\{([^}]*)\}", r"\1", s)

    # latex ops & functions
    s = s.replace(r"\times", "*").replace(r"\cdot", "*")
    s = s.replace("·", "*").replace("−", "-")
    s = s.replace(r"\max", "max").replace(r"\min", "min")
    s = s.replace(r"\log", "log").replace(r"\ln", "ln")

    # greek / latex names: \alpha -> alpha, \sigma -> sigma, etc.
    s = re.sub(r"\\([A-Za-z]+)", r"\1", s)

    # subscripts and bracketed variables: Z_\alpha -> Z_alpha, E[R_m] -> E_R_m
    s = s.replace("{", "").replace("}", "")
    s = s.replace("[", "_").replace("]", "")
    s = s.replace(" ", "")

    # \frac{A}{B}  (after braces removed) -> (A)/(B)
    # NOTE: with braces already removed, it will look like \fracA/B; handle both styles:
    s = re.sub(r"\\frac\(([^)]+)\)/\(([^)]+)\)", r"(\1)/(\2)", s)  # very rare
    s = re.sub(r"\\frac([^/]+)/([^/]+)", r"(\1)/(\2)", s)

    # exponentials and powers
    s = re.sub(r"e\^\(([^)]+)\)", r"exp(\1)", s)    # e^(...)
    s = re.sub(r"e\^([A-Za-z0-9_\.]+)", r"exp(\1)", s)  # e^x
    s = s.replace("^", "**")   # simple powers

    return s

def eval_formula(latex: str, vars_map: dict) -> float:
    expr = latex_to_python(latex)
    # build safe scope
    scope = {k: float(v) for k, v in vars_map.items()}
    val = eval(expr, {"__builtins__": None, **ALLOWED}, scope)
    return float(f"{float(val):.4f}")

@app.route("/trading-formula", methods=["POST", "OPTIONS"], strict_slashes=False)
def trading_formula():
    if request.method == "OPTIONS":
        return ("", 204)

    payload = request.get_json(silent=True)
    if payload is None:
        try:
            payload = json.loads((request.data or b"").decode("utf-8"))
        except Exception:
            return jsonify(error="Expected JSON array body"), 400

    if not isinstance(payload, list):
        return jsonify(error="Body must be a JSON array of testcases"), 400

    out = []
    for t in payload:
        try:
            res = eval_formula(t["formula"], t.get("variables", {}))
            out.append({"result": res})
        except Exception:
        
            out.append({"result": 0.0})
    return jsonify(out), 200
