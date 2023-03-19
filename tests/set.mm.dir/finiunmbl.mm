include "cfn.mm"
include "wcel.mm"
include "cvol.mm"
include "cdm.mm"
include "wral.mm"
include "ciun.mm"
include "cv.mm"
include "wi.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "raleq.mm"
include "iuneq1.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "weq.mm"
include "0iun.mm"
include "0mbl.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wss.mm"
include "ssun1.mm"
include "ssralv.mm"
include "ax-mp.mm"
include "imim1i.mm"
include "ssun2.mm"
include "wa.mm"
include "iunxun.mm"
include "csb.mm"
include "vex.mm"
include "csbeq1.mm"
include "ralsn.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "csbeq1a.mm"
include "cbvral.mm"
include "nfcv.mm"
include "cbviun.mm"
include "iunxsn.mm"
include "eqtri.mm"
include "eleq1i.mm"
include "3bitr4i.mm"
include "unmbl.mm"
include "sylan2b.mm"
include "syl5eqel.mm"
include "expcom.mm"
include "syl.mm"
include "sylcom.mm"
include "findcard2.mm"
include "imp.mm"

theorem finiunmbl
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint A k
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- ( ( A e. Fin /\ A. k e. A B e. dom vol ) -> U_ k e. A B e. dom vol )

  proof
    cA
    cfn
    wcel
    cB
    cvol
    cdm
    #
    wcel
    #
    vk
    cA
    wral
    #
    vk
    cA
    cB
    ciun
    #
    @0
    wcel
    #
    @1
    vk
    vy
    cv
    #
    wral
    #
    vk
    @5
    cB
    ciun
    #
    @0
    wcel
    #
    wi
    @1
    vk
    c0
    wral
    #
    vk
    c0
    cB
    ciun
    #
    @0
    wcel
    #
    wi
    @1
    vk
    vx
    cv
    #
    wral
    #
    vk
    @12
    cB
    ciun
    #
    @0
    wcel
    #
    wi
    #
    @1
    vk
    @12
    vz
    cv
    #
    csn
    #
    cun
    #
    wral
    #
    vk
    @19
    cB
    ciun
    #
    @0
    wcel
    #
    wi
    #
    @2
    @4
    wi
    vy
    vx
    vz
    cA
    @5
    c0
    wceq
    #
    @6
    @9
    @8
    @11
    @1
    vk
    @5
    c0
    raleq
    @24
    @7
    @10
    @0
    vk
    @5
    c0
    cB
    iuneq1
    eleq1d
    imbi12d
    vy
    vx
    weq
    #
    @6
    @13
    @8
    @15
    @1
    vk
    @5
    @12
    raleq
    @25
    @7
    @14
    @0
    vk
    @5
    @12
    cB
    iuneq1
    eleq1d
    imbi12d
    @5
    @19
    wceq
    #
    @6
    @20
    @8
    @22
    @1
    vk
    @5
    @19
    raleq
    @26
    @7
    @21
    @0
    vk
    @5
    @19
    cB
    iuneq1
    eleq1d
    imbi12d
    @5
    cA
    wceq
    #
    @6
    @2
    @8
    @4
    @1
    vk
    @5
    cA
    raleq
    @27
    @7
    @3
    @0
    vk
    @5
    cA
    cB
    iuneq1
    eleq1d
    imbi12d
    @11
    @9
    @10
    c0
    @0
    vk
    cB
    0iun
    0mbl
    eqeltri
    a1i
    @16
    @23
    wi
    @12
    cfn
    wcel
    @16
    @20
    @15
    @22
    @20
    @13
    @15
    @12
    @19
    wss
    @20
    @13
    wi
    @12
    @18
    ssun1
    @1
    vk
    @12
    @19
    ssralv
    ax-mp
    imim1i
    @20
    @1
    vk
    @18
    wral
    #
    @15
    @22
    wi
    @18
    @19
    wss
    @20
    @28
    wi
    @18
    @12
    ssun2
    @1
    vk
    @18
    @19
    ssralv
    ax-mp
    @15
    @28
    @22
    @15
    @28
    wa
    @21
    @14
    vk
    @18
    cB
    ciun
    #
    cun
    #
    @0
    vk
    @12
    @18
    cB
    iunxun
    @28
    @15
    @29
    @0
    wcel
    #
    @30
    @0
    wcel
    vk
    @12
    cB
    csb
    #
    @0
    wcel
    #
    vx
    @18
    wral
    vk
    @17
    cB
    csb
    #
    @0
    wcel
    #
    @28
    @31
    @33
    @35
    vx
    @17
    vz
    vex
    #
    vx
    vz
    weq
    @32
    @34
    @0
    vk
    @12
    @17
    cB
    csbeq1
    #
    eleq1d
    ralsn
    @1
    @33
    vk
    vx
    @18
    @1
    vx
    nfv
    vk
    @32
    @0
    vk
    @12
    cB
    nfcsb1v
    #
    nfel1
    vk
    vx
    weq
    cB
    @32
    @0
    vk
    @12
    cB
    csbeq1a
    #
    eleq1d
    cbvral
    @29
    @34
    @0
    @29
    vx
    @18
    @32
    ciun
    @34
    vk
    vx
    @18
    cB
    @32
    vx
    cB
    nfcv
    @38
    @39
    cbviun
    vx
    @17
    @32
    @34
    @36
    @37
    iunxsn
    eqtri
    eleq1i
    3bitr4i
    @14
    @29
    unmbl
    sylan2b
    syl5eqel
    expcom
    syl
    sylcom
    a1i
    findcard2
    imp
end
