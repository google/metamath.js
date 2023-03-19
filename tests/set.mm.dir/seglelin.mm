include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wo.mm"
include "ccgr.mm"
include "wrex.mm"
include "csegle.mm"
include "segcon2.mm"
include "andir.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "simpr.mm"
include "simpl3.mm"
include "cgrcom.mm"
include "syl121anc.mm"
include "anbi2d.mm"
include "orbi2d.mm"
include "syl5bb.mm"
include "rexbidva.mm"
include "brsegle2.mm"
include "brsegle.mm"
include "3com23.mm"
include "orbi12d.mm"
include "r19.43.mm"
include "syl6bbr.mm"
include "bitr4d.mm"
include "mpbid.mm"

theorem seglelin
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N
  let vx: setvar x


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( <. A , B >. Seg<_ <. C , D >. \/ <. C , D >. Seg<_ <. A , B >. ) )

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
    wa
    #
    cC
    @1
    wcel
    cD
    @1
    wcel
    wa
    #
    w3a
    #
    cB
    cA
    vx
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    @7
    cA
    cB
    cop
    #
    cbtwn
    wbr
    #
    wo
    @8
    cC
    cD
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
    @10
    @12
    csegle
    wbr
    #
    @12
    @10
    csegle
    wbr
    #
    wo
    #
    vx
    cB
    cC
    cD
    cA
    cN
    segcon2
    @6
    @15
    @9
    @13
    wa
    #
    @11
    @12
    @8
    ccgr
    wbr
    #
    wa
    #
    wo
    #
    vx
    @1
    wrex
    #
    @18
    @6
    @14
    @22
    vx
    @1
    @14
    @19
    @11
    @13
    wa
    #
    wo
    @6
    @7
    @1
    wcel
    #
    wa
    #
    @22
    @9
    @11
    @13
    andir
    @26
    @24
    @21
    @19
    @26
    @13
    @20
    @11
    @26
    @0
    @2
    @25
    @5
    @13
    @20
    wb
    @0
    @4
    @5
    @25
    simpl1
    @2
    @3
    @0
    @5
    @25
    simpl2l
    @6
    @25
    simpr
    @0
    @4
    @5
    @25
    simpl3
    cA
    @7
    cC
    cD
    cN
    cgrcom
    syl121anc
    anbi2d
    orbi2d
    syl5bb
    rexbidva
    @6
    @18
    @19
    vx
    @1
    wrex
    #
    @21
    vx
    @1
    wrex
    #
    wo
    @23
    @6
    @16
    @27
    @17
    @28
    vx
    cA
    cB
    cC
    cD
    cN
    brsegle2
    @0
    @5
    @4
    @17
    @28
    wb
    vx
    cC
    cD
    cA
    cB
    cN
    brsegle
    3com23
    orbi12d
    @19
    @21
    vx
    @1
    r19.43
    syl6bbr
    bitr4d
    mpbid
end
