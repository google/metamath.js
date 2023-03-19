include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cxp.mm"
include "cres.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "opelxpi.mm"
include "fvres.mm"
include "syl.mm"
include "df-ov.mm"
include "3eqtr4g.mm"

theorem ovres
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F


  assert |- ( ( A e. C /\ B e. D ) -> ( A ( F |` ( C X. D ) ) B ) = ( A F B ) )

  proof
    cA
    cC
    wcel
    cB
    cD
    wcel
    wa
    #
    cA
    cB
    cop
    #
    cF
    cC
    cD
    cxp
    #
    cres
    #
    cfv
    #
    @1
    cF
    cfv
    #
    cA
    cB
    @3
    co
    cA
    cB
    cF
    co
    @0
    @1
    @2
    wcel
    @4
    @5
    wceq
    cA
    cB
    cC
    cD
    opelxpi
    @1
    @2
    cF
    fvres
    syl
    cA
    cB
    @3
    df-ov
    cA
    cB
    cF
    df-ov
    3eqtr4g
end
