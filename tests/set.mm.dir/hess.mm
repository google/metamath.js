include "wss.mm"
include "cima.mm"
include "whe.mm"
include "wi.mm"
include "imass1.mm"
include "sstr2.mm"
include "syl.mm"
include "df-he.mm"
include "3imtr4g.mm"

theorem hess
  let cA: class A
  let cR: class R
  let cS: class S


  assert |- ( S C_ R -> ( R hereditary A -> S hereditary A ) )

  proof
    cS
    cR
    wss
    #
    cR
    cA
    cima
    #
    cA
    wss
    #
    cS
    cA
    cima
    #
    cA
    wss
    #
    cA
    cR
    whe
    cA
    cS
    whe
    @0
    @3
    @1
    wss
    @2
    @4
    wi
    cS
    cR
    cA
    imass1
    @3
    @1
    cA
    sstr2
    syl
    cA
    cR
    df-he
    cA
    cS
    df-he
    3imtr4g
end
