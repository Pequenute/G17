# /// script
# dependencies = [
#     "marimo>=0.23.11",
#     "z3-solver",
# ]
# requires-python = ">=3.14"
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="medium")


@app.cell
def _():
    import marimo as mo
    import z3
    import time
    import ast
    import pathlib

    return ast, mo, pathlib, time, z3


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # Exclusão mútua num anel com testemunho

    $N$ processos em anel; o processo $i$ tem três booleanos: $w_i$ (à espera), $c_i$ (na secção crítica) e $t_i$ (tem o testemunho).
    Inicialmente todos estão inativos e só o processo $0$ tem o testemunho. Em cada transição **um** processo $i$ move-se
    (com $n=(i+1) \bmod N$):

    | regra | guarda | efeito |
    |---|---|---|
    | pedir | $\neg w_i \wedge \neg c_i$ | $w_i := 1$ |
    | entrar | $w_i \wedge t_i$ | $w_i := 0,\ c_i := 1$ |
    | sair | $c_i$ | $c_i := 0,\ t_i := 0,\ t_n := 1$ |
    | passar | $\neg w_i \wedge \neg c_i \wedge t_i$ | $t_i := 0,\ t_n := 1$ |
    | regenerar *(variante)* | $w_i \wedge \neg t_i$ | $t_i := 1$ |

    Estado de erro: $\bigvee_{i<j} c_i \wedge c_j$.

    **Requisito:** `pdr_lia.py` (o ficheiro fornecido) tem de estar na mesma pasta deste notebook.
    Resultados: `sat` = existe invariante (seguro) · `unsat` = erro alcançável · `unknown` = limite atingido.
    """)
    return


@app.cell
def _(z3):
    class Anel:
        """SFOTS do anel com testemunho. inteiros=True usa variáveis em {0,1} (o PDR de pdr_lia.py só trabalha com inteiros)."""

        def __init__(self, N, regenerar=False, inteiros=False):
            self.N, self.inteiros = N, inteiros
            mk = z3.Int if inteiros else z3.Bool
            self._mk = mk
            self.nomes = [f"{v}{i}" for i in range(N) for v in "wct"]   # w0 c0 t0 w1 c1 t1 ...
            self.X = [mk(n) for n in self.nomes]
            self.Xp = [mk(n + "'") for n in self.nomes]
            v = lambda nome: self.X[self.nomes.index(nome)]
            self.movs = []
            for i in range(N):
                w, c, t, n = v(f"w{i}"), v(f"c{i}"), v(f"t{i}"), (i + 1) % N
                inativo = z3.And(self.F(w), self.F(c))
                self.movs += [
                    (f"pedir({i})", self._mov(inativo, {f"w{i}": 1})),
                    (f"entrar({i})", self._mov(z3.And(self.T(w), self.T(t)), {f"w{i}": 0, f"c{i}": 1})),
                    (f"sair({i})", self._mov(self.T(c), {f"c{i}": 0, f"t{i}": 0, f"t{n}": 1})),
                    (f"passar({i})", self._mov(z3.And(inativo, self.T(t)), {f"t{i}": 0, f"t{n}": 1})),
                ]
                if regenerar:
                    self.movs.append((f"regenerar({i})", self._mov(z3.And(self.T(w), self.F(t)), {f"t{i}": 1})))
            self.trans = z3.Or([f for _, f in self.movs])
            self.init = z3.And(
                [self.T(v(f"t{i}")) if i == 0 else self.F(v(f"t{i}")) for i in range(N)]
                + [self.F(v(f"{x}{i}")) for i in range(N) for x in "wc"]
                + ([self._dom(self.X)] if inteiros else [])
            )
            self.mau = z3.Or([z3.And(self.T(v(f"c{i}")), self.T(v(f"c{j}")))
                              for i in range(N) for j in range(i + 1, N)])

        def T(self, v):
            return v == 1 if self.inteiros else v

        def F(self, v):
            return v == 0 if self.inteiros else z3.Not(v)

        def _dom(self, vs):
            return z3.And([z3.And(x >= 0, x <= 1) for x in vs])

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
            return z3.And(
                [z3.Or(self.F(v(f"t{i}")), self.F(v(f"t{j}"))) for i in range(self.N) for j in range(i + 1, self.N)]
                + [z3.Or(self.F(v(f"c{i}")), self.T(v(f"t{i}"))) for i in range(self.N)]
            )

        # cópias do estado (desdobramento no tempo) e renomeações
        def copia(self, k):
            return [self._mk(f"{n}@{k}") for n in self.nomes]

        def em(self, f, V):                     # f(X) -> f(V)
            return z3.substitute(f, *zip(self.X, V))

        def linha(self, f):                     # f(X) -> f(X')
            return z3.substitute(f, *zip(self.X, self.Xp))

        def de(self, f, V):                     # f(V) -> f(X)
            return z3.substitute(f, *zip(V, self.X))

        def passo(self, f, V, W):               # f(X,X') -> f(V,W)
            return z3.substitute(f, *zip(self.X, V), *zip(self.Xp, W))

    return (Anel,)


@app.cell
def _(z3):
    def e_unsat(*fs):
        s = z3.Solver()
        s.add(*fs)
        return s.check() == z3.unsat

    def verifica_invariante(S, inv):
        """Verificação independente: Init ⇒ I,  I ∧ T ⇒ I',  I ∧ Mau insatisfazível."""
        return {
            "inicial": e_unsat(S.init, z3.Not(inv)),
            "indutivo": e_unsat(inv, S.trans, z3.Not(S.linha(inv))),
            "seguro": e_unsat(inv, S.mau),
        }

    def tamanho(f):
        """(nº de cláusulas, nº de nós) do invariante."""
        f = z3.simplify(f)
        vistos, pilha = set(), [f]
        while pilha:
            e = pilha.pop()
            if e.get_id() not in vistos:
                vistos.add(e.get_id())
                pilha.extend(e.children())
        return (len(f.children()) if z3.is_and(f) else 1), len(vistos)

    def traco(S, m, E):
        """Traço (estados E segundo o modelo m): regra aplicada + estado (W/C/T por processo)."""
        val = lambda x: z3.is_true(m.eval(x, model_completion=True))
        linhas = []
        for j, V in enumerate(E):
            regra = "início" if j == 0 else next(
                (r for r, f in S.movs if val(S.passo(f, E[j - 1], V))), "?")
            est = " ".join("".join(c if val(V[3 * i + k]) else "-" for k, c in enumerate("WCT"))
                           for i in range(S.N))
            linhas.append(f"{j:3d}  {regra:13s} {est}")
        return "\n".join(linhas)

    return e_unsat, tamanho, traco, verifica_invariante


@app.cell
def _(traco, z3):
    def bmc(S, kmax):
        """Menor k <= kmax com Init ∧ T^k ∧ Mau(X_k) satisfazível: (k, modelo, estados) ou (None, None, None)."""
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
        """Passo: ¬Mau(X0) ∧ T ∧ ... ∧ ¬Mau(X_{k-1}) ∧ T ∧ Mau(Xk) insatisfazível?  (caso base: BMC)"""
        k0, m, E = bmc(S, kmax)
        if k0 is not None:
            return f"caso base falha: erro em {k0} passos\n" + traco(S, m, E[: k0 + 1])
        out = []
        for k in range(1, kmax + 1):
            E = [S.copia(j) for j in range(k + 1)]
            s = z3.Solver()
            for j in range(k):
                s.add(z3.Not(S.em(S.mau, E[j])), S.passo(S.trans, E[j], E[j + 1]))
            s.add(S.em(S.mau, E[k]))
            if simples:
                s.add([z3.Or([x != y for x, y in zip(E[a], E[b])])
                       for a in range(k + 1) for b in range(a + 1, k + 1)])
            if s.check() == z3.unsat:
                out.append(f"k={k}: passo indutivo UNSAT -> propriedade provada por {k}-indução")
                return "\n".join(out)
            out.append(f"k={k}: passo indutivo SAT (a {k}-indução falha)")
            if k in (1, 3):
                out.append(f"   contra-exemplo ao passo ({k} estados seguros + 1 de erro; W=espera C=crítica T=testemunho):")
                out.append(traco(S, s.model(), E))
        out.append(f"não provado até k={kmax}")
        return "\n".join(out)

    return bmc, k_inducao


@app.cell
def _(e_unsat, time, z3):
    def spacer(S, tempo):
        """O sistema de CHC's  Init→P,  P∧T→P',  P∧Mau→⊥  entregue ao Spacer."""
        P = z3.Function("P", *[z3.BoolSort()] * len(S.X), z3.BoolSort())
        s = z3.SolverFor("HORN")
        s.set("timeout", int(tempo * 1000))
        s.add(
            z3.ForAll(S.X, z3.Implies(S.init, P(*S.X))),
            z3.ForAll(S.X + S.Xp, z3.Implies(z3.And(P(*S.X), S.trans), P(*S.Xp))),
            z3.ForAll(S.X, z3.Implies(z3.And(P(*S.X), S.mau), False)),
        )
        r = s.check()
        return str(r), (z3.simplify(s.model().eval(P(*S.X))) if r == z3.sat else None), "n/d"

    def _interpolante(A, B, vars_A, vars_B, comum, ms):
        """Interpolante de Craig via CHC's:  ∀ A → I(comum)  e  ∀ I(comum) ∧ B → ⊥  (resolvidas pelo Spacer)."""
        I = z3.Function("I", *[v.sort() for v in comum], z3.BoolSort())
        s = z3.SolverFor("HORN")
        s.set("timeout", max(1000, int(ms)))
        s.add(z3.ForAll(vars_A, z3.Implies(A, I(*comum))),
              z3.ForAll(vars_B, z3.Implies(z3.And(I(*comum), B), False)))
        if s.check() != z3.sat:
            raise RuntimeError("sem interpolante (limite de tempo?)")
        return z3.simplify(s.model().eval(I(*comum)))

    def itp(S, tempo, kmax=40):
        """
        Interpolantes e invariantes (McMillan).
        R := Init;  A := R(X0) ∧ T(X0,X1);  B := T(X1,X2) ∧ ... ∧ T(X_{k-1},Xk) ∧ (Mau(X1) ∨ ... ∨ Mau(Xk)).
        A∧B sat: se R = Init é um erro real; senão k++ e recomeça.
        A∧B unsat: I := interpolante(A,B); se I ⇒ R, R é invariante indutivo; senão R := R ∨ I.
        """
        prazo, n, k = time.time() + tempo, 0, 0
        if not e_unsat(S.init, S.mau):
            return "unsat", None, "k=0"
        for k in range(1, kmax + 1):
            R, primeiro = S.init, True
            while time.time() < prazo:
                E = [S.copia(j) for j in range(k + 1)]
                A = z3.And(S.em(R, E[0]), S.passo(S.trans, E[0], E[1]))
                B = z3.And([S.passo(S.trans, E[j], E[j + 1]) for j in range(1, k)]
                           + [z3.Or([S.em(S.mau, E[j]) for j in range(1, k + 1)])])
                if not e_unsat(A, B):
                    if primeiro:
                        return "unsat", None, f"k={k}, {n} interpolantes"
                    break                                        # R grosseiro demais: aumenta k
                I = S.de(_interpolante(A, B, E[0] + E[1], [x for V in E[1:] for x in V], E[1],
                                       (prazo - time.time()) * 1000), E[1])
                n += 1
                if e_unsat(I, z3.Not(R)):                        # I ⇒ R: ponto fixo
                    return "sat", z3.simplify(R), f"k={k}, {n} interpolantes"
                R, primeiro = z3.Or(R, I), False
            else:
                break
        return "unknown", None, f"k={k}, {n} interpolantes"

    return itp, spacer


@app.cell
def _(Anel, ast, mo, pathlib, time, z3):
    def _carregar_pdr():
        """pdr_lia.py é um notebook marimo: executa só as células que definem CFA, PDR, ... (sem a interface)."""
        pasta = mo.notebook_dir() or pathlib.Path.cwd()
        caminho = pathlib.Path(pasta) / "pdr_lia.py"
        ns, queremos = {"z3": z3, "time": time}, {"CFA", "PDR", "Limite", "mbp", "literais", "conj"}
        for nd in ast.parse(caminho.read_text(encoding="utf-8")).body:
            if isinstance(nd, ast.FunctionDef) and any(ast.unparse(d).startswith("app.cell") for d in nd.decorator_list):
                corpo = [x for x in nd.body if not isinstance(x, ast.Return)]
                if {x.name for x in corpo if isinstance(x, (ast.FunctionDef, ast.ClassDef))} & queremos:
                    exec(compile(ast.Module(body=corpo, type_ignores=[]), str(caminho), "exec"), ns)
        return ns

    def pdr(N, regenerar, tempo, max_passos=20000):
        """PDR de pdr_lia.py sobre o CFA  system --init--> loop --T--> loop --Mau--> error  (inteiros em {0,1})."""
        ns = _carregar_pdr()
        Si = Anel(N, regenerar, inteiros=True)
        S = ns["CFA"](Si.nomes, {
            ("system", "loop"): Si.linha(Si.init),
            ("loop", "loop"): Si.trans,
            ("loop", "error"): z3.And([Si.mau, Si._dom(Si.X)] + [xp == x for x, xp in zip(Si.X, Si.Xp)]),
        }, "anel")
        prazo = time.time() + tempo

        class ComTempo(ns["PDR"]):                      # só acrescenta um limite de tempo
            def tem_predecessor(self, cubo, l, i):
                if time.time() > prazo:
                    raise ns["Limite"]
                return super().tem_predecessor(cubo, l, i)

        p = ComTempo(S, max_N=4 * N + 10, max_passos=max_passos)
        res, test = p.resolve()
        inv = None
        if res == "sat":                                # inteiros {0,1} -> booleanos: n ↦ If(b,1,0)
            Sb = Anel(N, regenerar)
            inv = z3.simplify(z3.substitute(
                test["loop"], *[(z3.Int(n), z3.If(b, z3.IntVal(1), z3.IntVal(0))) for n, b in zip(Sb.nomes, Sb.X)]))
        return res, inv, f"{p.N} frames, {p.passos} obrigações"

    return (pdr,)


@app.cell
def _(Anel, itp, pdr, spacer, tamanho, time, verifica_invariante):
    def corre_todos(N, regenerar, tempo):
        """Corre interpolantes, Spacer e PDR. Devolve (linhas da tabela, {algoritmo: invariante})."""
        S = Anel(N, regenerar)
        linhas, invs = [], {}
        for nome, f, args in (("interpolantes", itp, (S, tempo)),
                              ("spacer", spacer, (S, tempo)),
                              ("pdr", pdr, (N, regenerar, tempo))):
            t0 = time.time()
            try:
                res, inv, it = f(*args)
            except Exception as e:                       # noqa: BLE001
                res, inv, it = "erro", None, repr(e)[:60]
            linha = {"N": N, "algoritmo": nome, "resultado": res, "tempo (s)": round(time.time() - t0, 2),
                     "iterações": it, "cláusulas": "", "nós": "", "verificado": ""}
            if inv is not None:
                linha["cláusulas"], linha["nós"] = tamanho(inv)
                linha["verificado"] = all(verifica_invariante(S, inv).values())
                invs[nome] = inv
            linhas.append(linha)
        return linhas, invs

    return (corre_todos,)


@app.cell(hide_code=True)
def _(mo):
    N = mo.ui.slider(2, 8, value=3, label="N (nº de processos)", debounce=True)
    kmax = mo.ui.slider(1, 12, value=6, label="k máximo (k-indução)")
    simples = mo.ui.checkbox(label="k-indução com simple path")
    tempo = mo.ui.number(10, 3600, value=300, label="limite (s) por algoritmo")
    Ns = mo.ui.multiselect(options=["2", "3", "4", "5", "6", "7"], value=["2", "3", "4"], label="N no benchmark")
    variante_bench = mo.ui.checkbox(label="benchmark da variante (insegura)")
    mo.vstack([mo.md("## Parâmetros"), mo.hstack([N, kmax, simples], justify="start"),
               mo.hstack([tempo, Ns, variante_bench], justify="start")])
    return N, Ns, kmax, simples, tempo, variante_bench


@app.cell(hide_code=True)
def _(Anel, N, mo, verifica_invariante):
    _S = Anel(N.value)
    _v = verifica_invariante(_S, _S.inv_maos())
    mo.md(f"""
    ## 1. O modelo

    Com $N={N.value}$: **{len(_S.X)} variáveis booleanas** e **{len(_S.movs)} regras** (uma por processo e tipo).
    Exemplo — regras do processo 0: `{", ".join(r for r, _ in _S.movs if r.endswith("(0)"))}`.

    Verificação ao Z3 do invariante escrito à mão *«no máximo um testemunho ∧ cᵢ → tᵢ»* (serve também de teste ao modelo):
    `{_v}`
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    btn_kind = mo.ui.run_button(label="Executar k-indução")
    mo.vstack([mo.md("""
    ## 2. A k-indução falha

    A propriedade «nunca há dois processos na secção crítica» **não é indutiva**: há estados seguros mas inalcançáveis
    (p. ex. um processo na secção crítica sem testemunho) que passam a um estado de erro num só passo.
    Para $N\\geq 3$ há ainda um ciclo de estados seguros e inalcançáveis com **dois testemunhos** a circular,
    por isso o passo indutivo é satisfazível para qualquer $k$ (verificado por enumeração para $N\\leq 5$).
    """), btn_kind])
    return (btn_kind,)


@app.cell
def _(Anel, N, btn_kind, k_inducao, kmax, mo, simples):
    mo.stop(not btn_kind.value, mo.md("Carrega em «Executar k-indução»"))
    _S = Anel(N.value)
    mo.md("```text\n" + k_inducao(_S, kmax.value, simples.value) + "\n```")
    return


@app.cell(hide_code=True)
def _(mo):
    btn_seg = mo.ui.run_button(label="Executar PDR, interpolantes e Spacer")
    mo.vstack([mo.md("""
    ## 3. Segurança com invariante indutivo

    Cada invariante extraído é **verificado de forma independente** com consultas novas ao Z3 sobre o SFOTS booleano:
    $\\mathit{Init}\\Rightarrow I$, $I\\wedge T\\Rightarrow I'$ e $I\\wedge\\mathit{Mau}$ insatisfazível.
    """), btn_seg])
    return (btn_seg,)


@app.cell
def _(N, btn_seg, corre_todos, mo, tempo):
    mo.stop(not btn_seg.value, mo.md("*Carrega no botão para correr os três algoritmos.*"))
    _linhas, _invs = corre_todos(N.value, False, tempo.value)
    _acc = mo.accordion({
        f"invariante de {k}": mo.md("```text\n" + str(v) + "\n```")
        for k, v in _invs.items() if len(str(v)) < 3000
    })
    mo.vstack([mo.ui.table(_linhas, selection=None), _acc])
    return


@app.cell(hide_code=True)
def _(mo):
    btn_var = mo.ui.run_button(label="Executar a variante")
    mo.vstack([mo.md("""
    ## 4. Variante com regeneração de testemunho

    Um processo à espera e sem testemunho pode regenerá-lo: o erro passa a ser alcançável. Os três algoritmos
    devem dar `unsat`; abaixo, o traço mais curto obtido com BMC (5 passos, por enumeração, para qualquer $N\\geq 2$).
    """), btn_var])
    return (btn_var,)


@app.cell
def _(Anel, N, bmc, btn_var, corre_todos, mo, tempo, traco):
    mo.stop(not btn_var.value, mo.md("*Carrega em «Executar a variante».*"))
    _S = Anel(N.value, True)
    _k, _m, _E = bmc(_S, 12)
    _linhas, _ = corre_todos(N.value, True, tempo.value)
    mo.vstack([
        mo.ui.table(_linhas, selection=None),
        mo.md(f"**Traço de erro mais curto (BMC): {_k} passos** (W=espera, C=crítica, T=testemunho)\n\n```text\n"
              + traco(_S, _m, _E) + "\n```"),
    ])
    return


@app.cell(hide_code=True)
def _(mo):
    btn_bench = mo.ui.run_button(label="Executar o benchmark")
    mo.vstack([mo.md("""
    ## 5. Comparação para $N$ crescente

    Tempo, iterações e dimensão do invariante do PDR, do algoritmo de interpolantes e do Spacer
    (sequencialmente, com o limite de tempo por algoritmo definido acima).
    """), btn_bench])
    return (btn_bench,)


@app.cell
def _(Ns, btn_bench, corre_todos, mo, tempo, variante_bench):
    mo.stop(not btn_bench.value, mo.md("*Escolhe os N e carrega em «Executar o benchmark».*"))
    _linhas = []
    for _n in sorted(int(x) for x in Ns.value):
        _l, _ = corre_todos(_n, variante_bench.value, tempo.value)
        _linhas += _l
    mo.ui.table(_linhas, selection=None)
    return


if __name__ == "__main__":
    app.run()
