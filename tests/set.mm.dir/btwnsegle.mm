include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "csegle.mm"
include "cv.mm"
include "ccgr.mm"
include "wrex.mm"
include "simplr2.mm"
include "simpr.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "cgrrflxd.mm"
include "adantr.mm"
include "wceq.mm"
include "breq1.mm"
include "opeq2.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "wb.mm"
include "simpr3.mm"
include "brsegle.mm"
include "syl122anc.mm"
include "mpbird.mm"
include "ex.mm"

theorem btwnsegle
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N
  let vx: setvar x


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) -> ( B Btwn <. A , C >. -> <. A , B >. Seg<_ <. A , C >. ) )

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
    cB
    cA
    cC
    cop
    #
    cbtwn
    wbr
    #
    cA
    cB
    cop
    #
    @7
    csegle
    wbr
    #
    @6
    @8
    wa
    #
    @10
    vx
    cv
    #
    @7
    cbtwn
    wbr
    #
    @9
    cA
    @12
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    vx
    @1
    wrex
    #
    @11
    @3
    @8
    @9
    @9
    ccgr
    wbr
    #
    @17
    @2
    @3
    @4
    @0
    @8
    simplr2
    @6
    @8
    simpr
    @6
    @18
    @8
    @6
    cA
    cB
    cN
    @0
    @5
    simpl
    #
    @0
    @2
    @3
    @4
    simpr1
    #
    @0
    @2
    @3
    @4
    simpr2
    #
    cgrrflxd
    adantr
    @16
    @8
    @18
    wa
    vx
    cB
    @1
    @12
    cB
    wceq
    #
    @13
    @8
    @15
    @18
    @12
    cB
    @7
    cbtwn
    breq1
    @22
    @14
    @9
    @9
    ccgr
    @12
    cB
    cA
    opeq2
    breq2d
    anbi12d
    rspcev
    syl12anc
    @6
    @10
    @17
    wb
    #
    @8
    @6
    @0
    @2
    @3
    @2
    @4
    @23
    @19
    @20
    @21
    @20
    @0
    @2
    @3
    @4
    simpr3
    vx
    cA
    cB
    cA
    cC
    cN
    brsegle
    syl122anc
    adantr
    mpbird
    ex
end
