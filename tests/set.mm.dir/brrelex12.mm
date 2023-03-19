include "wrel.mm"
include "wbr.mm"
include "wa.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "wss.mm"
include "df-rel.mm"
include "biimpi.mm"
include "ssbrd.mm"
include "imp.mm"
include "brxp.mm"
include "sylib.mm"

theorem brrelex12
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( ( Rel R /\ A R B ) -> ( A e. _V /\ B e. _V ) )

  proof
    cR
    wrel
    #
    cA
    cB
    cR
    wbr
    #
    wa
    cA
    cB
    cvv
    cvv
    cxp
    #
    wbr
    #
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    wa
    @0
    @1
    @3
    @0
    cR
    @2
    cA
    cB
    @0
    cR
    @2
    wss
    cR
    df-rel
    biimpi
    ssbrd
    imp
    cA
    cB
    cvv
    cvv
    brxp
    sylib
end
