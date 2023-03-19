include "ccom.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "wral.mm"
include "cotrg.mm"
include "nfv.mm"
include "19.21-2.mm"
include "albii.mm"
include "w3a.mm"
include "simpl.mm"
include "id.mm"
include "simpr.mm"
include "3jca.mm"
include "simp2.mm"
include "impbii.mm"
include "cdm.mm"
include "vex.mm"
include "breldm.mm"
include "sseldi.mm"
include "pm4.71ri.mm"
include "crn.mm"
include "cin.mm"
include "brelrn.mm"
include "elin.mm"
include "biimpri.mm"
include "syl2an.mm"
include "3anbi123i.mm"
include "3an6.mm"
include "anbi2i.mm"
include "bitri.mm"
include "3bitri.mm"
include "imbi1i.mm"
include "impexp.mm"
include "3impexp.mm"
include "2albii.mm"
include "df-ral.mm"
include "3bitr4i.mm"
include "19.21v.mm"
include "bicomi.mm"
include "ralbii.mm"

theorem cotr2g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  assume cotr2g.d: |- dom B C_ D
  assume cotr2g.e: |- ( ran B i^i dom A ) C_ E
  assume cotr2g.f: |- ran A C_ F

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint E y
  disjoint E z
  disjoint F z
  assert |- ( ( A o. B ) C_ C <-> A. x e. D A. y e. E A. z e. F ( ( x B y /\ y A z ) -> x C z ) )

  proof
    cA
    cB
    ccom
    cC
    wss
    vx
    cv
    #
    vy
    cv
    #
    cB
    wbr
    #
    @1
    vz
    cv
    #
    cA
    wbr
    #
    wa
    #
    @0
    @3
    cC
    wbr
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    #
    @3
    cF
    wcel
    #
    @7
    wi
    #
    vz
    wal
    #
    vy
    cE
    wral
    #
    vx
    cD
    wral
    #
    @7
    vz
    cF
    wral
    #
    vy
    cE
    wral
    #
    vx
    cD
    wral
    vx
    vy
    vz
    cA
    cB
    cC
    cotrg
    @9
    @1
    cE
    wcel
    #
    @11
    wi
    #
    vz
    wal
    #
    vy
    wal
    #
    vx
    cD
    wral
    #
    @14
    @0
    cD
    wcel
    #
    @18
    wi
    #
    vz
    wal
    #
    vy
    wal
    #
    vx
    wal
    @22
    @20
    wi
    #
    vx
    wal
    @9
    @21
    @25
    @26
    vx
    @22
    @18
    vy
    vz
    @22
    vy
    nfv
    @22
    vz
    nfv
    19.21-2
    albii
    @8
    @24
    vx
    vy
    @7
    @23
    vz
    @7
    @22
    @17
    @10
    w3a
    #
    @5
    wa
    #
    @6
    wi
    @27
    @7
    wi
    @23
    @5
    @28
    @6
    @5
    @2
    @5
    @4
    w3a
    #
    @22
    @2
    wa
    #
    @17
    @5
    wa
    #
    @10
    @4
    wa
    #
    w3a
    #
    @28
    @5
    @29
    @5
    @2
    @5
    @4
    @2
    @4
    simpl
    @5
    id
    @2
    @4
    simpr
    3jca
    #
    @2
    @5
    @4
    simp2
    #
    impbii
    @2
    @30
    @5
    @31
    @4
    @32
    @2
    @22
    @2
    cB
    cdm
    cD
    @0
    cotr2g.d
    @0
    @1
    cB
    vx
    vex
    #
    vy
    vex
    #
    breldm
    sseldi
    pm4.71ri
    @5
    @17
    @5
    cB
    crn
    #
    cA
    cdm
    #
    cin
    #
    cE
    @1
    cotr2g.e
    @2
    @1
    @38
    wcel
    #
    @1
    @39
    wcel
    #
    @1
    @40
    wcel
    #
    @4
    @0
    @1
    cB
    @36
    @37
    brelrn
    @1
    @3
    cA
    @37
    vz
    vex
    #
    breldm
    @43
    @41
    @42
    wa
    @1
    @38
    @39
    elin
    biimpri
    syl2an
    sseldi
    pm4.71ri
    @4
    @10
    @4
    cA
    crn
    cF
    @3
    cotr2g.f
    @1
    @3
    cA
    @37
    @44
    brelrn
    sseldi
    pm4.71ri
    3anbi123i
    @33
    @27
    @29
    wa
    @28
    @22
    @2
    @17
    @5
    @10
    @4
    3an6
    @29
    @5
    @27
    @29
    @5
    @35
    @34
    impbii
    anbi2i
    bitri
    3bitri
    imbi1i
    @27
    @5
    @6
    impexp
    @22
    @17
    @10
    @7
    3impexp
    3bitri
    albii
    2albii
    @20
    vx
    cD
    df-ral
    3bitr4i
    @20
    @13
    vx
    cD
    @13
    @20
    @13
    @17
    @12
    wi
    #
    vy
    wal
    @20
    @12
    vy
    cE
    df-ral
    @45
    @19
    vy
    @19
    @45
    @17
    @11
    vz
    19.21v
    bicomi
    albii
    bitri
    bicomi
    ralbii
    bitri
    @13
    @16
    vx
    cD
    @12
    @15
    vy
    cE
    @15
    @12
    @7
    vz
    cF
    df-ral
    bicomi
    ralbii
    ralbii
    3bitri
end
