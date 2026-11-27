# /// script
# dependencies = ["marimo", "z3-solver"]
# requires-python = ">=3.14"
# ///

#!/usr/bin/env python3
"""
Exclusão mútua num anel com testemunho (Z3).   pdr_lia.py tem de estar na mesma pasta.

  python anel.py kind      --N 3 --kmax 6      # (2) a k-indução falha; mostra o CTI
  python anel.py seguranca --N 3               # (3) interpolantes, Spacer e PDR + invariantes verificados
  python anel.py variante  --N 3               # (4) regeneração de testemunho: erro + traço BMC
  python anel.py bench --Ns 2 3 4 5            # (5) comparação para N crescente   [--variante]

Resultado: "sat" = existe invariante (seguro) | "unsat" = erro alcançável | "unknown" = limite atingido.
"""
import argparse
import ast
import os
import time

import z3


# ============================================================================
# 1. O SFOTS.  Variáveis do processo i: w_i (espera), c_i (secção crítica), t_i (testemunho).
#    pedir    : ¬w ∧ ¬c      → w := 1
#    entrar   : w ∧ t        → w := 0, c := 1
#    sair     : c            → c := 0, t_i := 0, t_{i+1} := 1
#    passar   : ¬w ∧ ¬c ∧ t  → t_i := 0, t_{i+1} := 1
#    regenerar: w ∧ ¬t       → t := 1                      (só na variante)
#  Um processo move-se por transição; o resto fica igual.
#  inteiros=True usa variáveis em {0,1} (o PDR de pdr_lia.py só trabalha com inteiros).
# ============================================================================
class Anel:
    def __init__(self, N, regenerar=False, inteiros=False):
        self.N, self.inteiros = N, inteiros
        mk = z3.Int if inteiros else z3.Bool
        self.nomes = [f"{v}{i}" for i in range(N) for v in "wct"]           # w0 c0 t0 w1 c1 t1 ...
        self.X = [mk(n) for n in self.nomes]
        self.Xp = [mk(n + "'") for n in self.nomes]
        self._mk = mk
        v = lambda nome: self.X[self.nomes.index(nome)]
        self.movs = []
        for i in range(N):
            w, c, t, n = v(f"w{i}"), v(f"c{i}"), v(f"t{i}"), (i + 1) % N
            inativo = z3.And(self.F(w), self.F(c))
            self.movs += [(f"pedir({i})", self._mov(inativo, {f"w{i}": 1})),
                          (f"entrar({i})", self._mov(z3.And(self.T(w), self.T(t)), {f"w{i}": 0, f"c{i}": 1})),
                          (f"sair({i})", self._mov(self.T(c), {f"c{i}": 0, f"t{i}": 0, f"t{n}": 1})),
                          (f"passar({i})", self._mov(z3.And(inativo, self.T(t)), {f"t{i}": 0, f"t{n}": 1}))]
            if regenerar:
                self.movs.append((f"regenerar({i})", self._mov(z3.And(self.T(w), self.F(t)), {f"t{i}": 1})))
        self.trans = z3.Or([f for _, f in self.movs])
        self.init = z3.And([self.T(v(f"t{i}")) if i == 0 else self.F(v(f"t{i}")) for i in range(N)] +
                           [self.F(v(f"{x}{i}")) for i in range(N) for x in "wc"] +
                           ([self._dom(self.X)] if inteiros else []))
        self.mau = z3.Or([z3.And(self.T(v(f"c{i}")), self.T(v(f"c{j}")))
                          for i in range(N) for j in range(i + 1, N)])

    def T(self, v): return v == 1 if self.inteiros else v
    def F(self, v): return v == 0 if self.inteiros else z3.Not(v)
    def _dom(self, vs): return z3.And([z3.And(x >= 0, x <= 1) for x in vs])

    def _mov(self, guarda, mud):
        """guarda ∧ (variáveis em `mud` := constante) ∧ (as outras ficam iguais)"""
        cs = [guarda]
        for n, x, xp in zip(self.nomes, self.X, self.Xp):
            if n not in mud:
                cs.append(xp == x)
            elif self.inteiros:
                cs.append(xp == mud[n])
            else:
                cs.append(xp if mud[n] else z3.Not(xp))
        if self.inteiros:
            cs += [self._dom(self.X), self._dom(self.Xp)]
        return z3.And(cs)

    def inv_maos(self):
        """Invariante à mão: no máximo um testemunho ∧ (c_i → t_i)."""
        v = lambda nome: self.X[self.nomes.index(nome)]
        return z3.And([z3.Or(self.F(v(f"t{i}")), self.F(v(f"t{j}"))) for i in range(self.N) for j in range(i + 1, self.N)] +
                      [z3.Or(self.F(v(f"c{i}")), self.T(v(f"t{i}"))) for i in range(self.N)])

    # cópias do estado (desdobramento no tempo) e renomeações
    def copia(self, k): return [self._mk(f"{n}@{k}") for n in self.nomes]
    def em(self, f, V): return z3.substitute(f, *zip(self.X, V))                     # f(X) -> f(V)
    def linha(self, f): return z3.substitute(f, *zip(self.X, self.Xp))               # f(X) -> f(X')
    def de(self, f, V): return z3.substitute(f, *zip(V, self.X))                     # f(V) -> f(X)
    def passo(self, f, V, W): return z3.substitute(f, *zip(self.X, V), *zip(self.Xp, W))   # f(V,W)


# ============================================================================
# Utilitários
# ============================================================================
def e_unsat(*fs):
    s = z3.Solver()
    s.add(*fs)
    return s.check() == z3.unsat


def verifica_invariante(S, inv):
    """Verificação independente: Init ⇒ I,  I ∧ T ⇒ I',  I ∧ Mau insatisfazível."""
    return {"inicial": e_unsat(S.init, z3.Not(inv)),
            "indutivo": e_unsat(inv, S.trans, z3.Not(S.linha(inv))),
            "seguro": e_unsat(inv, S.mau)}


def tamanho(f):
    """(nº de cláusulas, nº de nós) do invariante."""
    f, vistos, pilha = z3.simplify(f), set(), [z3.simplify(f)]
    while pilha:
        e = pilha.pop()
        if e.get_id() not in vistos:
            vistos.add(e.get_id())
            pilha.extend(e.children())
    return (len(f.children()) if z3.is_and(f) else 1), len(vistos)


def mostra(S, m, E):
    """Traço (lista de estados E) segundo o modelo m: regra aplicada + estado (W/C/T por processo)."""
    val = lambda x: z3.is_true(m.eval(x, model_completion=True))
    for j, V in enumerate(E):
        regra = "início" if j == 0 else next(
            (r for r, f in S.movs if val(S.passo(f, E[j - 1], V))), "?")
        est = " ".join("".join(c if val(V[3 * i + k]) else "-" for k, c in enumerate("WCT")) for i in range(S.N))
        print(f"   {j:2d}  {regra:13s} {est}")


# ============================================================================
# 2. BMC e k-indução
# ============================================================================
def bmc(S, kmax):
    s, E = z3.Solver(), [S.copia(0)]
    s.add(S.em(S.init, E[0]))
    for k in range(kmax + 1):
        s.push()
        s.add(S.em(S.mau, E[k]))
        if s.check() == z3.sat:
            return k, s.model(), E
        s.pop()
        E.append(S.copia(k + 1))
        s.add(S.passo(S.trans, E[k], E[k + 1]))
    return None, None, None


def k_inducao(S, kmax, simples=False):
    """Passo: ¬Mau(X0) ∧ T ∧ ... ∧ ¬Mau(X_{k-1}) ∧ T ∧ Mau(Xk) insatisfazível?  (+ BMC para o caso base)"""
    k0, m, E = bmc(S, kmax)
    if k0 is not None:
        print(f"caso base falha: erro em {k0} passos"); mostra(S, m, E[:k0 + 1]); return
    for k in range(1, kmax + 1):
        E = [S.copia(j) for j in range(k + 1)]
        s = z3.Solver()
        for j in range(k):
            s.add(z3.Not(S.em(S.mau, E[j])), S.passo(S.trans, E[j], E[j + 1]))
        s.add(S.em(S.mau, E[k]))
        if simples:
            s.add([z3.Or([x != y for x, y in zip(E[a], E[b])]) for a in range(k + 1) for b in range(a + 1, k + 1)])
        if s.check() == z3.unsat:
            print(f"k={k}: passo indutivo UNSAT -> propriedade provada por {k}-indução"); return
        print(f"k={k}: passo indutivo SAT (a {k}-indução falha)")
        if k in (1, 3):
            print(f"   contra-exemplo ao passo ({k} estados seguros + 1 de erro; W=espera C=crítica T=testemunho):")
            mostra(S, s.model(), E)
    print(f"não provado até k={kmax}")


# ============================================================================
# 3. Os três algoritmos de segurança.  Cada um devolve (resultado, invariante sobre S.X, iterações)
# ============================================================================
def spacer(S, tempo):
    """O sistema de CHC's Init→P, P∧T→P', P∧Mau→⊥ entregue ao Spacer."""
    P = z3.Function("P", *[z3.BoolSort()] * len(S.X), z3.BoolSort())
    s = z3.SolverFor("HORN")
    s.set("timeout", int(tempo * 1000))
    s.add(z3.ForAll(S.X, z3.Implies(S.init, P(*S.X))),
          z3.ForAll(S.X + S.Xp, z3.Implies(z3.And(P(*S.X), S.trans), P(*S.Xp))),
          z3.ForAll(S.X, z3.Implies(z3.And(P(*S.X), S.mau), False)))
    r = s.check()
    return str(r), (z3.simplify(s.model().eval(P(*S.X))) if r == z3.sat else None), "n/d"


def interpolante(A, B, vars_A, vars_B, comum, ms):
    """Interpolante de Craig via CHC's:  ∀ A → I(comum)   e   ∀ I(comum) ∧ B → ⊥   (resolvidas pelo Spacer)."""
    I = z3.Function("I", *[v.sort() for v in comum], z3.BoolSort())
    s = z3.SolverFor("HORN")
    s.set("timeout", max(1000, int(ms)))
    s.add(z3.ForAll(vars_A, z3.Implies(A, I(*comum))), z3.ForAll(vars_B, z3.Implies(z3.And(I(*comum), B), False)))
    if s.check() != z3.sat:
        raise RuntimeError("sem interpolante (limite de tempo?)")
    return z3.simplify(s.model().eval(I(*comum)))


def itp(S, tempo, kmax=40):
    """
    Interpolantes e invariantes (McMillan).  R := Init;  A := R(X0)∧T(X0,X1);  B := T(X1,X2)∧...∧T(X_{k-1},Xk) ∧ ∨_j Mau(Xj).
    A∧B sat: R=Init -> erro real; senão k++ e recomeça.   Unsat: I := interpolante(A,B); se I ⇒ R, R é invariante; senão R := R ∨ I.
    """
    prazo, n = time.time() + tempo, 0
    if not e_unsat(S.init, S.mau):
        return "unsat", None, "k=0"
    for k in range(1, kmax + 1):
        R, primeiro = S.init, True
        while time.time() < prazo:
            E = [S.copia(j) for j in range(k + 1)]
            A = z3.And(S.em(R, E[0]), S.passo(S.trans, E[0], E[1]))
            B = z3.And([S.passo(S.trans, E[j], E[j + 1]) for j in range(1, k)] +
                       [z3.Or([S.em(S.mau, E[j]) for j in range(1, k + 1)])])
            if not e_unsat(A, B):
                if primeiro:
                    return "unsat", None, f"k={k}, {n} interpolantes"
                break                                           # R sobre-aproximado demais: aumenta k
            I = S.de(interpolante(A, B, E[0] + E[1], [x for V in E[1:] for x in V], E[1],
                                  (prazo - time.time()) * 1000), E[1])
            n += 1
            if e_unsat(I, z3.Not(R)):                           # I ⇒ R: ponto fixo
                return "sat", z3.simplify(R), f"k={k}, {n} interpolantes"
            R, primeiro = z3.Or(R, I), False
        else:
            break
    return "unknown", None, f"k={k}, {n} interpolantes"


def carregar_pdr():
    """pdr_lia.py é um notebook marimo: executa só as células que definem CFA, PDR, ... (sem a interface)."""
    caminho = os.path.join(os.path.dirname(os.path.abspath(__file__)), "pdr_lia.py")
    ns, queremos = {"z3": z3, "time": time}, {"CFA", "PDR", "Limite", "mbp", "literais", "conj"}
    for nd in ast.parse(open(caminho, encoding="utf-8").read()).body:
        if isinstance(nd, ast.FunctionDef) and any(ast.unparse(d).startswith("app.cell") for d in nd.decorator_list):
            corpo = [x for x in nd.body if not isinstance(x, ast.Return)]
            if {x.name for x in corpo if isinstance(x, (ast.FunctionDef, ast.ClassDef))} & queremos:
                exec(compile(ast.Module(body=corpo, type_ignores=[]), caminho, "exec"), ns)
    return ns


def pdr(N, regenerar, tempo, max_passos=20000):
    """PDR de pdr_lia.py sobre o CFA  system --init--> loop --T--> loop --Mau--> error  (inteiros em {0,1})."""
    ns = carregar_pdr()
    Si = Anel(N, regenerar, inteiros=True)
    S = ns["CFA"](Si.nomes, {
        ("system", "loop"): Si.linha(Si.init),
        ("loop", "loop"): Si.trans,
        ("loop", "error"): z3.And([Si.mau, Si._dom(Si.X)] + [xp == x for x, xp in zip(Si.X, Si.Xp)])}, "anel")

    class ComTempo(ns["PDR"]):
        def tem_predecessor(self, cubo, l, i):
            if time.time() > prazo:
                raise ns["Limite"]
            return super().tem_predecessor(cubo, l, i)

    prazo = time.time() + tempo
    p = ComTempo(S, max_N=4 * N + 10, max_passos=max_passos)
    res, test = p.resolve()
    inv = None
    if res == "sat":                                            # inteiros {0,1} -> booleanos: n ↦ If(b,1,0)
        Sb = Anel(N, regenerar)
        inv = z3.simplify(z3.substitute(test["loop"], *[(z3.Int(n), z3.If(b, z3.IntVal(1), z3.IntVal(0))) for n, b in zip(Sb.nomes, Sb.X)]))
    return res, inv, f"{p.N} frames, {p.passos} obrigações"


def executa(nome, S, f, *args):
    t0 = time.time()
    res, inv, it = f(*args)
    linha = {"alg": nome, "res": res, "t": time.time() - t0, "it": it, "cl": "", "nos": "", "ok": ""}
    if inv is not None:
        linha["cl"], linha["nos"] = tamanho(inv)
        v = verifica_invariante(S, inv)
        linha["ok"] = all(v.values())
        linha["inv"] = inv
    return linha


def mostra_linha(r):
    print(f"  {r['alg']:7s} {r['res']:8s} {r['t']:7.2f}s  {r['it']:30s} invariante: {r['cl']} cláusulas / {r['nos']} nós, "
          f"verificado de forma independente: {r['ok']}")


def corre_todos(N, regenerar, tempo):
    S = Anel(N, regenerar)
    out = []
    for nome, f, args in (("itp", itp, (S, tempo)), ("spacer", spacer, (S, tempo)), ("pdr", pdr, (N, regenerar, tempo))):
        try:
            out.append(executa(nome, S, f, *args))
        except Exception as e:                                  # noqa: BLE001
            out.append({"alg": nome, "res": "erro", "t": 0, "it": repr(e)[:30], "cl": "", "nos": "", "ok": ""})
    return out


# ============================================================================
def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("cmd", choices=["kind", "seguranca", "variante", "bench"])
    p.add_argument("--N", type=int, default=3)
    p.add_argument("--Ns", type=int, nargs="+", default=[2, 3, 4, 5])
    p.add_argument("--kmax", type=int, default=6)
    p.add_argument("--simples", action="store_true", help="k-indução com 'simple path'")
    p.add_argument("--variante", action="store_true", help="bench com a variante insegura")
    p.add_argument("--tempo", type=int, default=300, help="limite (s) por algoritmo")
    a = p.parse_args()

    if a.cmd == "kind":
        S = Anel(a.N)
        print("invariante à mão (≤1 testemunho ∧ c→t) é indutivo e seguro:", verifica_invariante(S, S.inv_maos()))
        k_inducao(S, a.kmax, a.simples)
    elif a.cmd in ("seguranca", "variante"):
        reg = a.cmd == "variante"
        print(f"N={a.N}  {'variante com regeneração' if reg else 'sistema original'}")
        for r in corre_todos(a.N, reg, a.tempo):
            mostra_linha(r)
        if reg:
            S = Anel(a.N, True)
            k, m, E = bmc(S, 12)
            print(f"  traço de erro mais curto (BMC): {k} passos")
            mostra(S, m, E)
        else:
            S = Anel(a.N)
            print("  invariante à mão:", verifica_invariante(S, S.inv_maos()))
    else:
        print(f"{'N':>3} {'alg':>7} {'res':>8} {'tempo(s)':>9}  {'iterações':30s} {'cláus.':>7} {'nós':>6} {'verif.':>6}")
        for N in a.Ns:
            for r in corre_todos(N, a.variante, a.tempo):
                print(f"{N:>3} {r['alg']:>7} {r['res']:>8} {r['t']:>9.2f}  {r['it']:30s} {str(r['cl']):>7} {str(r['nos']):>6} {str(r['ok']):>6}",
                      flush=True)


if __name__ == "__main__":
    main()