include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "ccxp.mm"
include "cmul.mm"
include "cmin.mm"
include "cdiv.mm"
include "wceq.mm"
include "negcl.mm"
include "cxpadd.mm"
include "syl3an3.mm"
include "simp2.mm"
include "simp3.mm"
include "negsubd.mm"
include "oveq2d.mm"
include "c1.mm"
include "simp1l.mm"
include "simp1r.mm"
include "cxpneg.mm"
include "syl3anc.mm"
include "cxpcl.mm"
include "syl2anc.mm"
include "cxpne0.mm"
include "divrecd.mm"
include "eqtr4d.mm"
include "3eqtr3d.mm"

theorem cxpsub
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ B e. CC /\ C e. CC ) -> ( A ^c ( B - C ) ) = ( ( A ^c B ) / ( A ^c C ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    w3a
    #
    cA
    cB
    cC
    cneg
    #
    caddc
    co
    #
    ccxp
    co
    #
    cA
    cB
    ccxp
    co
    #
    cA
    @6
    ccxp
    co
    #
    cmul
    co
    #
    cA
    cB
    cC
    cmin
    co
    #
    ccxp
    co
    @9
    cA
    cC
    ccxp
    co
    #
    cdiv
    co
    #
    @4
    @2
    @3
    @6
    cc
    wcel
    @8
    @11
    wceq
    cC
    negcl
    cA
    cB
    @6
    cxpadd
    syl3an3
    @5
    @7
    @12
    cA
    ccxp
    @5
    cB
    cC
    @2
    @3
    @4
    simp2
    #
    @2
    @3
    @4
    simp3
    #
    negsubd
    oveq2d
    @5
    @11
    @9
    c1
    @13
    cdiv
    co
    #
    cmul
    co
    @14
    @5
    @10
    @17
    @9
    cmul
    @5
    @0
    @1
    @4
    @10
    @17
    wceq
    @0
    @1
    @3
    @4
    simp1l
    #
    @0
    @1
    @3
    @4
    simp1r
    #
    @16
    cA
    cC
    cxpneg
    syl3anc
    oveq2d
    @5
    @9
    @13
    @5
    @0
    @3
    @9
    cc
    wcel
    @18
    @15
    cA
    cB
    cxpcl
    syl2anc
    @5
    @0
    @4
    @13
    cc
    wcel
    @18
    @16
    cA
    cC
    cxpcl
    syl2anc
    @5
    @0
    @1
    @4
    @13
    cc0
    wne
    @18
    @19
    @16
    cA
    cC
    cxpne0
    syl3anc
    divrecd
    eqtr4d
    3eqtr3d
end
