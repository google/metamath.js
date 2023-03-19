include "cc0.mm"
include "c3.mm"
include "cfz.mm"
include "co.mm"
include "ci.mm"
include "cv.mm"
include "cexp.mm"
include "cr.mm"
include "wcel.mm"
include "cdiv.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "cmul.mm"
include "csu.mm"
include "citg.mm"
include "wceq.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfov.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfan.mm"
include "nfif.mm"
include "eleq1.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "ifbieq1d.mm"
include "cbvmpt.mm"
include "a1i.mm"
include "oveq2d.mm"
include "sumeq2i.mm"
include "eqid.mm"
include "dfitg.mm"
include "3eqtr4i.mm"

theorem cbvitg
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume cbvitg.1: |- ( x = y -> B = C )
  assume cbvitg.2: |- F/_ y B
  assume cbvitg.3: |- F/_ x C

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint B k
  disjoint C k
  assert |- S. A B _d x = S. A C _d y

  proof
    cc0
    c3
    cfz
    co
    #
    ci
    vk
    cv
    #
    cexp
    co
    #
    vx
    cr
    vx
    cv
    #
    cA
    wcel
    #
    cc0
    cB
    @2
    cdiv
    co
    #
    cre
    cfv
    #
    cle
    wbr
    #
    wa
    #
    @6
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cmul
    co
    #
    vk
    csu
    @0
    @2
    vy
    cr
    vy
    cv
    #
    cA
    wcel
    #
    cc0
    cC
    @2
    cdiv
    co
    #
    cre
    cfv
    #
    cle
    wbr
    #
    wa
    #
    @16
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cmul
    co
    #
    vk
    csu
    vx
    cA
    cB
    citg
    vy
    cA
    cC
    citg
    @0
    @12
    @22
    vk
    @1
    @0
    wcel
    #
    @11
    @21
    @2
    cmul
    @23
    @10
    @20
    citg2
    @10
    @20
    wceq
    @23
    vx
    vy
    cr
    @9
    @19
    @8
    vy
    @6
    cc0
    @4
    @7
    vy
    @4
    vy
    nfv
    vy
    cc0
    @6
    cle
    vy
    cc0
    nfcv
    #
    vy
    cle
    nfcv
    vy
    @5
    cre
    vy
    cre
    nfcv
    vy
    cB
    @2
    cdiv
    cbvitg.2
    vy
    cdiv
    nfcv
    vy
    @2
    nfcv
    nfov
    nffv
    #
    nfbr
    nfan
    @25
    @24
    nfif
    @18
    vx
    @16
    cc0
    @14
    @17
    vx
    @14
    vx
    nfv
    vx
    cc0
    @16
    cle
    vx
    cc0
    nfcv
    #
    vx
    cle
    nfcv
    vx
    @15
    cre
    vx
    cre
    nfcv
    vx
    cC
    @2
    cdiv
    cbvitg.3
    vx
    cdiv
    nfcv
    vx
    @2
    nfcv
    nfov
    nffv
    #
    nfbr
    nfan
    @27
    @26
    nfif
    @3
    @13
    wceq
    #
    @8
    @18
    @6
    @16
    cc0
    @28
    @4
    @14
    @7
    @17
    @3
    @13
    cA
    eleq1
    @28
    @6
    @16
    cc0
    cle
    @28
    @5
    @15
    cre
    @28
    cB
    cC
    @2
    cdiv
    cbvitg.1
    oveq1d
    fveq2d
    #
    breq2d
    anbi12d
    @29
    ifbieq1d
    cbvmpt
    a1i
    fveq2d
    oveq2d
    sumeq2i
    vx
    cA
    cB
    @6
    vk
    @6
    eqid
    dfitg
    vy
    cA
    cC
    @16
    vk
    @16
    eqid
    dfitg
    3eqtr4i
end
