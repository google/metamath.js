include "crpss.mm"
include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "wpss.mm"
include "wceq.mm"
include "w3o.mm"
include "wss.mm"
include "wo.mm"
include "wbr.mm"
include "solin.mm"
include "cvv.mm"
include "wb.mm"
include "elex.mm"
include "ad2antll.mm"
include "brrpssg.mm"
include "syl.mm"
include "biidd.mm"
include "ad2antrl.mm"
include "3orbi123d.mm"
include "mpbid.mm"
include "sspsstri.mm"
include "sylibr.mm"

theorem sorpssi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( [C.] Or A /\ ( B e. A /\ C e. A ) ) -> ( B C_ C \/ C C_ B ) )

  proof
    cA
    crpss
    wor
    #
    cB
    cA
    wcel
    #
    cC
    cA
    wcel
    #
    wa
    wa
    #
    cB
    cC
    wpss
    #
    cB
    cC
    wceq
    #
    cC
    cB
    wpss
    #
    w3o
    #
    cB
    cC
    wss
    cC
    cB
    wss
    wo
    @3
    cB
    cC
    crpss
    wbr
    #
    @5
    cC
    cB
    crpss
    wbr
    #
    w3o
    @7
    cA
    cB
    cC
    crpss
    solin
    @3
    @8
    @4
    @5
    @5
    @9
    @6
    @3
    cC
    cvv
    wcel
    #
    @8
    @4
    wb
    @2
    @10
    @0
    @1
    cC
    cA
    elex
    ad2antll
    cB
    cC
    cvv
    brrpssg
    syl
    @3
    @5
    biidd
    @3
    cB
    cvv
    wcel
    #
    @9
    @6
    wb
    @1
    @11
    @0
    @2
    cB
    cA
    elex
    ad2antrl
    cC
    cB
    cvv
    brrpssg
    syl
    3orbi123d
    mpbid
    cB
    cC
    sspsstri
    sylibr
end
