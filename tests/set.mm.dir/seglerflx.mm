include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cop.mm"
include "csegle.mm"
include "wbr.mm"
include "cv.mm"
include "cbtwn.mm"
include "ccgr.mm"
include "wa.mm"
include "wrex.mm"
include "simp3.mm"
include "btwntriv2.mm"
include "cgrrflx.mm"
include "wceq.mm"
include "breq1.mm"
include "opeq2.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "wb.mm"
include "simp1.mm"
include "simp2.mm"
include "brsegle.mm"
include "syl122anc.mm"
include "mpbird.mm"

theorem seglerflx
  let cA: class A
  let cB: class B
  let cN: class N
  let vy: setvar y


  assert |- ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) -> <. A , B >. Seg<_ <. A , B >. )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    w3a
    #
    cA
    cB
    cop
    #
    @5
    csegle
    wbr
    #
    vy
    cv
    #
    @5
    cbtwn
    wbr
    #
    @5
    cA
    @7
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    vy
    @1
    wrex
    #
    @4
    @3
    cB
    @5
    cbtwn
    wbr
    #
    @5
    @5
    ccgr
    wbr
    #
    @12
    @0
    @2
    @3
    simp3
    #
    cA
    cB
    cN
    btwntriv2
    cA
    cB
    cN
    cgrrflx
    @11
    @13
    @14
    wa
    vy
    cB
    @1
    @7
    cB
    wceq
    #
    @8
    @13
    @10
    @14
    @7
    cB
    @5
    cbtwn
    breq1
    @16
    @9
    @5
    @5
    ccgr
    @7
    cB
    cA
    opeq2
    breq2d
    anbi12d
    rspcev
    syl12anc
    @4
    @0
    @2
    @3
    @2
    @3
    @6
    @12
    wb
    @0
    @2
    @3
    simp1
    @0
    @2
    @3
    simp2
    #
    @15
    @17
    @15
    vy
    cA
    cB
    cA
    cB
    cN
    brsegle
    syl122anc
    mpbird
end
