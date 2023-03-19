include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "ccxp.mm"
include "co.mm"
include "cneg.mm"
include "c1.mm"
include "simp1.mm"
include "simp3.mm"
include "cxpcl.mm"
include "syl2anc.mm"
include "negcld.mm"
include "cxpne0.mm"
include "caddc.mm"
include "cmul.mm"
include "negidd.mm"
include "oveq2d.mm"
include "wceq.mm"
include "simp2.mm"
include "cxpadd.mm"
include "syl211anc.mm"
include "cxp0.mm"
include "syl.mm"
include "3eqtr3d.mm"
include "mvllmuld.mm"

theorem cxpneg
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ A =/= 0 /\ B e. CC ) -> ( A ^c -u B ) = ( 1 / ( A ^c B ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cB
    cc
    wcel
    #
    w3a
    #
    cA
    cB
    ccxp
    co
    #
    cA
    cB
    cneg
    #
    ccxp
    co
    #
    c1
    @3
    @0
    @2
    @4
    cc
    wcel
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp3
    #
    cA
    cB
    cxpcl
    syl2anc
    @3
    @0
    @5
    cc
    wcel
    #
    @6
    cc
    wcel
    @7
    @3
    cB
    @8
    negcld
    #
    cA
    @5
    cxpcl
    syl2anc
    cA
    cB
    cxpne0
    @3
    cA
    cB
    @5
    caddc
    co
    #
    ccxp
    co
    #
    cA
    cc0
    ccxp
    co
    #
    @4
    @6
    cmul
    co
    #
    c1
    @3
    @11
    cc0
    cA
    ccxp
    @3
    cB
    @8
    negidd
    oveq2d
    @3
    @0
    @1
    @2
    @9
    @12
    @14
    wceq
    @7
    @0
    @1
    @2
    simp2
    @8
    @10
    cA
    cB
    @5
    cxpadd
    syl211anc
    @3
    @0
    @13
    c1
    wceq
    @7
    cA
    cxp0
    syl
    3eqtr3d
    mvllmuld
end
