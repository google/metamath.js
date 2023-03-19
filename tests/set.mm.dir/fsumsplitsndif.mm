include "cfn.mm"
include "wcel.mm"
include "cz.mm"
include "wral.mm"
include "w3a.mm"
include "csu.mm"
include "csn.mm"
include "cdif.mm"
include "caddc.mm"
include "co.mm"
include "csb.mm"
include "cv.mm"
include "wn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "neldifsnd.mm"
include "disjsn.mm"
include "sylibr.mm"
include "cun.mm"
include "uncom.mm"
include "wss.mm"
include "simp2.mm"
include "snssd.mm"
include "undif.mm"
include "sylib.mm"
include "syl5req.mm"
include "simp1.mm"
include "cc.mm"
include "wi.mm"
include "wa.mm"
include "rspcsbela.mm"
include "zcnd.mm"
include "expcom.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "fsumsplit.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvsumi.mm"
include "oveq12i.mm"
include "3eqtr4g.mm"
include "3adant1.mm"
include "sumsns.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem fsumsplitsndif
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cX: class X
  let vx: setvar x

  disjoint A k
  disjoint X k
  disjoint A x
  disjoint k x
  disjoint B x
  disjoint X x
  disjoint k x
  assert |- ( ( A e. Fin /\ X e. A /\ A. k e. A B e. ZZ ) -> sum_ k e. A B = ( sum_ k e. ( A \ { X } ) B + [_ X / k ]_ B ) )

  proof
    cA
    cfn
    wcel
    #
    cX
    cA
    wcel
    #
    cB
    cz
    wcel
    vk
    cA
    wral
    #
    w3a
    #
    cA
    cB
    vk
    csu
    #
    cA
    cX
    csn
    #
    cdif
    #
    cB
    vk
    csu
    #
    @5
    cB
    vk
    csu
    #
    caddc
    co
    #
    @7
    vk
    cX
    cB
    csb
    #
    caddc
    co
    @3
    cA
    vk
    vx
    cv
    #
    cB
    csb
    #
    vx
    csu
    @6
    @12
    vx
    csu
    #
    @5
    @12
    vx
    csu
    #
    caddc
    co
    @4
    @9
    @3
    @6
    @5
    @12
    cA
    vx
    @3
    cX
    @6
    wcel
    wn
    @6
    @5
    cin
    c0
    wceq
    @3
    cX
    cA
    neldifsnd
    @6
    cX
    disjsn
    sylibr
    @3
    @6
    @5
    cun
    @5
    @6
    cun
    #
    cA
    @6
    @5
    uncom
    @3
    @5
    cA
    wss
    @15
    cA
    wceq
    @3
    cX
    cA
    @0
    @1
    @2
    simp2
    #
    snssd
    @5
    cA
    undif
    sylib
    syl5req
    @0
    @1
    @2
    simp1
    @3
    @11
    cA
    wcel
    #
    @12
    cc
    wcel
    #
    @2
    @0
    @17
    @18
    wi
    @1
    @17
    @2
    @18
    @17
    @2
    wa
    @12
    vk
    @11
    cA
    cB
    cz
    rspcsbela
    zcnd
    expcom
    3ad2ant3
    imp
    fsumsplit
    cA
    cB
    @12
    vk
    vx
    vx
    cB
    nfcv
    #
    vk
    @11
    cB
    nfcsb1v
    #
    vk
    @11
    cB
    csbeq1a
    #
    cbvsumi
    @7
    @13
    @8
    @14
    caddc
    @6
    cB
    @12
    vk
    vx
    @19
    @20
    @21
    cbvsumi
    @5
    cB
    @12
    vk
    vx
    @19
    @20
    @21
    cbvsumi
    oveq12i
    3eqtr4g
    @3
    @8
    @10
    @7
    caddc
    @3
    @1
    @10
    cc
    wcel
    #
    @8
    @10
    wceq
    @16
    @1
    @2
    @22
    @0
    @1
    @2
    wa
    @10
    vk
    cX
    cA
    cB
    cz
    rspcsbela
    zcnd
    3adant1
    cB
    vk
    cX
    cA
    sumsns
    syl2anc
    oveq2d
    eqtrd
end
