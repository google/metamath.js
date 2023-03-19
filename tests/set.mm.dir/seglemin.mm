include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "csegle.mm"
include "wbr.mm"
include "cv.mm"
include "cbtwn.mm"
include "ccgr.mm"
include "wrex.mm"
include "simpr2.mm"
include "btwntriv1.mm"
include "3adant3r1.mm"
include "cgrtriv.mm"
include "3adant3r3.mm"
include "wceq.mm"
include "breq1.mm"
include "opeq2.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "wb.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr3.mm"
include "brsegle.mm"
include "syl122anc.mm"
include "mpbird.mm"

theorem seglemin
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N
  let vy: setvar y


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) -> <. A , A >. Seg<_ <. B , C >. )

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
    cC
    @1
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cA
    cop
    #
    cB
    cC
    cop
    #
    csegle
    wbr
    #
    vy
    cv
    #
    @8
    cbtwn
    wbr
    #
    @7
    cB
    @10
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
    @6
    @3
    cB
    @8
    cbtwn
    wbr
    #
    @7
    cB
    cB
    cop
    #
    ccgr
    wbr
    #
    @15
    @0
    @2
    @3
    @4
    simpr2
    #
    @0
    @3
    @4
    @16
    @2
    cB
    cC
    cN
    btwntriv1
    3adant3r1
    @0
    @2
    @3
    @18
    @4
    cA
    cB
    cN
    cgrtriv
    3adant3r3
    @14
    @16
    @18
    wa
    vy
    cB
    @1
    @10
    cB
    wceq
    #
    @11
    @16
    @13
    @18
    @10
    cB
    @8
    cbtwn
    breq1
    @20
    @12
    @17
    @7
    ccgr
    @10
    cB
    cB
    opeq2
    breq2d
    anbi12d
    rspcev
    syl12anc
    @6
    @0
    @2
    @2
    @3
    @4
    @9
    @15
    wb
    @0
    @5
    simpl
    @0
    @2
    @3
    @4
    simpr1
    #
    @21
    @19
    @0
    @2
    @3
    @4
    simpr3
    vy
    cA
    cA
    cB
    cC
    cN
    brsegle
    syl122anc
    mpbird
end
