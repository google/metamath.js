include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "wpss.mm"
include "cv.mm"
include "wss.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wn.mm"
include "ccv.mm"
include "wbr.mm"
include "spansncv.mm"
include "3exp.mm"
include "com23.mm"
include "imp.mm"
include "ralrimiv.mm"
include "anim2i.mm"
include "expcom.mm"
include "wb.mm"
include "spansnch.mm"
include "chnle.mm"
include "sylan2.mm"
include "chjcl.mm"
include "cvbr2.mm"
include "syldan.mm"
include "3imtr4d.mm"

theorem spansncv2
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. CH /\ B e. ~H ) -> ( -. ( span ` { B } ) C_ A -> A <oH ( A vH ( span ` { B } ) ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    cA
    cA
    cB
    csn
    cspn
    cfv
    #
    chj
    co
    #
    wpss
    #
    @5
    cA
    vx
    cv
    #
    wpss
    @6
    @4
    wss
    wa
    @6
    @4
    wceq
    wi
    #
    vx
    cch
    wral
    #
    wa
    #
    @3
    cA
    wss
    wn
    #
    cA
    @4
    ccv
    wbr
    #
    @5
    @2
    @9
    @2
    @8
    @5
    @2
    @7
    vx
    cch
    @0
    @1
    @6
    cch
    wcel
    #
    @7
    wi
    @0
    @12
    @1
    @7
    @0
    @12
    @1
    @7
    cA
    @6
    cB
    spansncv
    3exp
    com23
    imp
    ralrimiv
    anim2i
    expcom
    @1
    @0
    @3
    cch
    wcel
    #
    @10
    @5
    wb
    cB
    spansnch
    #
    cA
    @3
    chnle
    sylan2
    @0
    @1
    @4
    cch
    wcel
    #
    @11
    @9
    wb
    @1
    @0
    @13
    @15
    @14
    cA
    @3
    chjcl
    sylan2
    vx
    cA
    @4
    cvbr2
    syldan
    3imtr4d
end
