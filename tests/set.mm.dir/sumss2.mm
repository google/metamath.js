include "wss.mm"
include "cc.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cuz.mm"
include "cfv.mm"
include "cfn.mm"
include "wo.mm"
include "cv.mm"
include "csb.mm"
include "cc0.mm"
include "cif.mm"
include "csu.mm"
include "wceq.mm"
include "simpll.mm"
include "simplr.mm"
include "iftrue.mm"
include "adantl.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "rspc.mm"
include "impcom.mm"
include "eqeltrd.mm"
include "sylan.mm"
include "cdif.mm"
include "eldifn.mm"
include "iffalsed.mm"
include "simpr.mm"
include "sumss.mm"
include "fsumss.mm"
include "jaodan.mm"
include "sumeq2i.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfif.mm"
include "eleq1.mm"
include "ifbieq1d.mm"
include "cbvsumi.mm"
include "eqtr3i.mm"
include "3eqtr4g.mm"

theorem sumss2
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cM: class M
  let vm: setvar m

  disjoint A k
  disjoint B k
  disjoint k m
  disjoint A m
  disjoint B m
  disjoint C m
  disjoint M m
  assert |- ( ( ( A C_ B /\ A. k e. A C e. CC ) /\ ( B C_ ( ZZ>= ` M ) \/ B e. Fin ) ) -> sum_ k e. A C = sum_ k e. B if ( k e. A , C , 0 ) )

  proof
    cA
    cB
    wss
    #
    cC
    cc
    wcel
    #
    vk
    cA
    wral
    #
    wa
    #
    cB
    cM
    cuz
    cfv
    wss
    #
    cB
    cfn
    wcel
    #
    wo
    wa
    cA
    vm
    cv
    #
    cA
    wcel
    #
    vk
    @6
    cC
    csb
    #
    cc0
    cif
    #
    vm
    csu
    #
    cB
    @9
    vm
    csu
    #
    cA
    cC
    vk
    csu
    #
    cB
    vk
    cv
    #
    cA
    wcel
    #
    cC
    cc0
    cif
    #
    vk
    csu
    @3
    @4
    @10
    @11
    wceq
    @5
    @3
    @4
    wa
    #
    cA
    cB
    @9
    vm
    cM
    @0
    @2
    @4
    simpll
    @16
    @2
    @7
    @9
    cc
    wcel
    #
    @0
    @2
    @4
    simplr
    @2
    @7
    wa
    @9
    @8
    cc
    @7
    @9
    @8
    wceq
    @2
    @7
    @8
    cc0
    iftrue
    adantl
    @7
    @2
    @8
    cc
    wcel
    #
    @1
    @18
    vk
    @6
    cA
    vk
    @8
    cc
    vk
    @6
    cC
    nfcsb1v
    #
    nfel1
    @13
    @6
    wceq
    #
    cC
    @8
    cc
    vk
    @6
    cC
    csbeq1a
    #
    eleq1d
    rspc
    impcom
    eqeltrd
    #
    sylan
    @6
    cB
    cA
    cdif
    wcel
    #
    @9
    cc0
    wceq
    #
    @16
    @23
    @7
    @8
    cc0
    @6
    cB
    cA
    eldifn
    iffalsed
    #
    adantl
    @3
    @4
    simpr
    sumss
    @3
    @5
    wa
    #
    cA
    cB
    @9
    vm
    @0
    @2
    @5
    simpll
    @26
    @2
    @7
    @17
    @0
    @2
    @5
    simplr
    @22
    sylan
    @23
    @24
    @26
    @25
    adantl
    @3
    @5
    simpr
    fsumss
    jaodan
    cA
    @15
    vk
    csu
    @12
    @10
    cA
    @15
    cC
    vk
    @14
    cC
    cc0
    iftrue
    sumeq2i
    cA
    @15
    @9
    vk
    vm
    vm
    @15
    nfcv
    #
    @7
    vk
    @8
    cc0
    @7
    vk
    nfv
    @19
    vk
    cc0
    nfcv
    nfif
    #
    @20
    @14
    @7
    cC
    @8
    cc0
    @13
    @6
    cA
    eleq1
    @21
    ifbieq1d
    #
    cbvsumi
    eqtr3i
    cB
    @15
    @9
    vk
    vm
    @27
    @28
    @29
    cbvsumi
    3eqtr4g
end
