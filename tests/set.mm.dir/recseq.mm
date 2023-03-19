include "wceq.mm"
include "con0.mm"
include "cep.mm"
include "cwrecs.mm"
include "crecs.mm"
include "wrecseq3.mm"
include "df-recs.mm"
include "3eqtr4g.mm"

theorem recseq
  let cF: class F
  let cG: class G


  assert |- ( F = G -> recs ( F ) = recs ( G ) )

  proof
    cF
    cG
    wceq
    con0
    cep
    cF
    cwrecs
    con0
    cep
    cG
    cwrecs
    cF
    crecs
    cG
    crecs
    con0
    cep
    cF
    cG
    wrecseq3
    cF
    df-recs
    cG
    df-recs
    3eqtr4g
end
