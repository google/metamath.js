include "cch.mm"
include "wcel.mm"
include "ccv.mm"
include "wbr.mm"
include "wpss.mm"
include "wa.mm"
include "wn.mm"
include "wi.mm"
include "cv.mm"
include "wrex.mm"
include "cvbr.mm"
include "wceq.mm"
include "psseq2.mm"
include "psseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "ex.mm"
include "con3rr3.mm"
include "adantl.mm"
include "syl6bi.mm"
include "com23.mm"
include "3impia.mm"

theorem cvnbtwn
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. CH /\ B e. CH /\ C e. CH ) -> ( A <oH B -> -. ( A C. C /\ C C. B ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cC
    cch
    wcel
    #
    cA
    cB
    ccv
    wbr
    #
    cA
    cC
    wpss
    #
    cC
    cB
    wpss
    #
    wa
    #
    wn
    #
    wi
    @0
    @1
    wa
    #
    @3
    @2
    @7
    @8
    @3
    cA
    cB
    wpss
    #
    cA
    vx
    cv
    #
    wpss
    #
    @10
    cB
    wpss
    #
    wa
    #
    vx
    cch
    wrex
    #
    wn
    #
    wa
    @2
    @7
    wi
    #
    vx
    cA
    cB
    cvbr
    @15
    @16
    @9
    @2
    @6
    @14
    @2
    @6
    @14
    @13
    @6
    vx
    cC
    cch
    @10
    cC
    wceq
    @11
    @4
    @12
    @5
    @10
    cC
    cA
    psseq2
    @10
    cC
    cB
    psseq1
    anbi12d
    rspcev
    ex
    con3rr3
    adantl
    syl6bi
    com23
    3impia
end
