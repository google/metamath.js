include "chlo.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "cnv.mm"
include "hlnv.mm"
include "dipcj.mm"
include "syl3an1.mm"
include "3com23.mm"
include "eqcomd.mm"

theorem hlipcj
  let cA: class A
  let cB: class B
  let cP: class P
  let cU: class U
  let cX: class X
  assume hlipf.1: |- X = ( BaseSet ` U )
  assume hlipf.7: |- P = ( .iOLD ` U )


  assert |- ( ( U e. CHilOLD /\ A e. X /\ B e. X ) -> ( A P B ) = ( * ` ( B P A ) ) )

  proof
    cU
    chlo
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    cB
    cA
    cP
    co
    ccj
    cfv
    #
    cA
    cB
    cP
    co
    #
    @0
    @2
    @1
    @3
    @4
    wceq
    #
    @0
    cU
    cnv
    wcel
    @2
    @1
    @5
    cU
    hlnv
    cB
    cA
    cP
    cU
    cX
    hlipf.1
    hlipf.7
    dipcj
    syl3an1
    3com23
    eqcomd
end
