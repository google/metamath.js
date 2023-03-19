include "cfn.mm"
include "wcel.mm"
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
include "0iun.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "0fin.mm"
include "a1i.mm"
include "wss.mm"
include "ssun1.mm"
include "ssralv.mm"
include "ax-mp.mm"
include "imim1i.mm"
include "wa.mm"
include "iunxun.mm"
include "csb.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbviun.mm"
include "vex.mm"
include "csbeq1.mm"
include "iunxsn.mm"
include "eqtri.mm"
include "ssun2.mm"
include "vsnid.mm"
include "sselii.mm"
include "nfel1.mm"
include "rspc.mm"
include "syl5eqel.mm"
include "unfi.mm"
include "sylan2.mm"
include "expcom.mm"
include "sylcom.mm"
include "findcard2.mm"
include "imp.mm"

theorem iunfi
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B y
  disjoint B z
  assert |- ( ( A e. Fin /\ A. x e. A B e. Fin ) -> U_ x e. A B e. Fin )

  proof
    cA
    cfn
    wcel
    cB
    cfn
    wcel
    #
    vx
    cA
    wral
    #
    vx
    cA
    cB
    ciun
    #
    cfn
    wcel
    #
    @0
    vx
    vw
    cv
    #
    wral
    #
    vx
    @4
    cB
    ciun
    #
    cfn
    wcel
    #
    wi
    @0
    vx
    c0
    wral
    #
    c0
    cfn
    wcel
    #
    wi
    @0
    vx
    vy
    cv
    #
    wral
    #
    vx
    @10
    cB
    ciun
    #
    cfn
    wcel
    #
    wi
    #
    @0
    vx
    @10
    vz
    cv
    #
    csn
    #
    cun
    #
    wral
    #
    vx
    @17
    cB
    ciun
    #
    cfn
    wcel
    #
    wi
    #
    @1
    @3
    wi
    vw
    vy
    vz
    cA
    @4
    c0
    wceq
    #
    @5
    @8
    @7
    @9
    @0
    vx
    @4
    c0
    raleq
    @22
    @6
    c0
    cfn
    @22
    @6
    vx
    c0
    cB
    ciun
    c0
    vx
    @4
    c0
    cB
    iuneq1
    vx
    cB
    0iun
    syl6eq
    eleq1d
    imbi12d
    @4
    @10
    wceq
    #
    @5
    @11
    @7
    @13
    @0
    vx
    @4
    @10
    raleq
    @23
    @6
    @12
    cfn
    vx
    @4
    @10
    cB
    iuneq1
    eleq1d
    imbi12d
    @4
    @17
    wceq
    #
    @5
    @18
    @7
    @20
    @0
    vx
    @4
    @17
    raleq
    @24
    @6
    @19
    cfn
    vx
    @4
    @17
    cB
    iuneq1
    eleq1d
    imbi12d
    @4
    cA
    wceq
    #
    @5
    @1
    @7
    @3
    @0
    vx
    @4
    cA
    raleq
    @25
    @6
    @2
    cfn
    vx
    @4
    cA
    cB
    iuneq1
    eleq1d
    imbi12d
    @9
    @8
    0fin
    a1i
    @14
    @21
    wi
    @10
    cfn
    wcel
    @14
    @18
    @13
    @20
    @18
    @11
    @13
    @10
    @17
    wss
    @18
    @11
    wi
    @10
    @16
    ssun1
    @0
    vx
    @10
    @17
    ssralv
    ax-mp
    imim1i
    @13
    @18
    @20
    @13
    @18
    wa
    @19
    @12
    vx
    @16
    cB
    ciun
    #
    cun
    #
    cfn
    vx
    @10
    @16
    cB
    iunxun
    @18
    @13
    @26
    cfn
    wcel
    @27
    cfn
    wcel
    @18
    @26
    vx
    @15
    cB
    csb
    #
    cfn
    @26
    vy
    @16
    vx
    @10
    cB
    csb
    #
    ciun
    @28
    vx
    vy
    @16
    cB
    @29
    vy
    cB
    nfcv
    vx
    @10
    cB
    nfcsb1v
    vx
    @10
    cB
    csbeq1a
    cbviun
    vy
    @15
    @29
    @28
    vz
    vex
    vx
    @10
    @15
    cB
    csbeq1
    iunxsn
    eqtri
    @15
    @17
    wcel
    @18
    @28
    cfn
    wcel
    #
    wi
    @16
    @17
    @15
    @16
    @10
    ssun2
    vz
    vsnid
    sselii
    @0
    @30
    vx
    @15
    @17
    vx
    @28
    cfn
    vx
    @15
    cB
    nfcsb1v
    nfel1
    vx
    cv
    @15
    wceq
    cB
    @28
    cfn
    vx
    @15
    cB
    csbeq1a
    eleq1d
    rspc
    ax-mp
    syl5eqel
    @12
    @26
    unfi
    sylan2
    syl5eqel
    expcom
    sylcom
    a1i
    findcard2
    imp
end
