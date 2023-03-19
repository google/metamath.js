include "cz.mm"
include "wss.mm"
include "cv.mm"
include "cc0.mm"
include "wne.mm"
include "wrex.mm"
include "wa.mm"
include "c0.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "c1.mm"
include "wcel.mm"
include "cdvds.mm"
include "1z.mm"
include "ssel.mm"
include "1dvds.mm"
include "syl6.mm"
include "ralrimiv.mm"
include "wceq.mm"
include "breq1.mm"
include "ralbidv.mm"
include "elrab2.mm"
include "biimpri.mm"
include "sylancr.mm"
include "ne0i.mm"
include "syl.mm"
include "adantr.mm"
include "neeq1.mm"
include "cbvrexv.mm"
include "wi.mm"
include "cabs.mm"
include "cfv.mm"
include "simprbi.mm"
include "adantl.mm"
include "simplbi.mm"
include "ssel2.mm"
include "dvdsleabs.mm"
include "3expia.mm"
include "sylan2.mm"
include "anassrs.mm"
include "com23.mm"
include "ralrimiva.mm"
include "ancoms.mm"
include "r19.26.mm"
include "pm3.35.mm"
include "ralimi.mm"
include "sylbir.mm"
include "syl2anc.mm"
include "fveq2.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "ralbii.mm"
include "ralcom.mm"
include "r19.21v.mm"
include "3bitri.mm"
include "sylib.mm"
include "cn0.mm"
include "nn0abscl.mm"
include "nn0zd.mm"
include "wb.mm"
include "breq2.mm"
include "rspcedv.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "mpd.mm"
include "r19.23v.mm"
include "imp.mm"
include "sylan2b.mm"
include "jca.mm"

theorem gcdcllem1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cS: class S
  let vn: setvar n
  let vw: setvar w
  assume gcdcllem1.1: |- S = { z e. ZZ | A. n e. A z || n }

  disjoint A n
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint S x
  disjoint A w
  disjoint n w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint S w
  assert |- ( ( A C_ ZZ /\ E. n e. A n =/= 0 ) -> ( S =/= (/) /\ E. x e. ZZ A. y e. S y <_ x ) )

  proof
    cA
    cz
    wss
    #
    vn
    cv
    #
    cc0
    wne
    #
    vn
    cA
    wrex
    #
    wa
    cS
    c0
    wne
    #
    vy
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vy
    cS
    wral
    #
    vx
    cz
    wrex
    #
    @0
    @4
    @3
    @0
    c1
    cS
    wcel
    #
    @4
    @0
    c1
    cz
    wcel
    #
    c1
    @1
    cdvds
    wbr
    #
    vn
    cA
    wral
    #
    @10
    1z
    @0
    @12
    vn
    cA
    @0
    @1
    cA
    wcel
    #
    @1
    cz
    wcel
    #
    @12
    cA
    cz
    @1
    ssel
    @1
    1dvds
    syl6
    ralrimiv
    @10
    @11
    @13
    wa
    vz
    cv
    #
    @1
    cdvds
    wbr
    #
    vn
    cA
    wral
    #
    @13
    vz
    c1
    cz
    cS
    @16
    c1
    wceq
    @17
    @12
    vn
    cA
    @16
    c1
    @1
    cdvds
    breq1
    ralbidv
    gcdcllem1.1
    elrab2
    biimpri
    sylancr
    cS
    c1
    ne0i
    syl
    adantr
    @3
    @0
    vw
    cv
    #
    cc0
    wne
    #
    vw
    cA
    wrex
    #
    @9
    @2
    @20
    vn
    vw
    cA
    @1
    @19
    cc0
    neeq1
    #
    cbvrexv
    @0
    @21
    @9
    @0
    @20
    @9
    wi
    #
    vw
    cA
    wral
    #
    @21
    @9
    wi
    @0
    @20
    @5
    @19
    cabs
    cfv
    #
    cle
    wbr
    #
    vy
    cS
    wral
    #
    wi
    #
    vw
    cA
    wral
    #
    @24
    @0
    @2
    @5
    @1
    cabs
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vn
    cA
    wral
    #
    vy
    cS
    wral
    #
    @29
    @0
    @33
    vy
    cS
    @0
    @5
    cS
    wcel
    #
    wa
    @5
    @1
    cdvds
    wbr
    #
    vn
    cA
    wral
    #
    @36
    @32
    wi
    #
    vn
    cA
    wral
    #
    @33
    @35
    @37
    @0
    @35
    @5
    cz
    wcel
    #
    @37
    @18
    @37
    vz
    @5
    cz
    cS
    @16
    @5
    wceq
    @17
    @36
    vn
    cA
    @16
    @5
    @1
    cdvds
    breq1
    ralbidv
    gcdcllem1.1
    elrab2
    #
    simprbi
    adantl
    @35
    @0
    @40
    @39
    @35
    @40
    @37
    @41
    simplbi
    @40
    @0
    @39
    @40
    @0
    wa
    #
    @38
    vn
    cA
    @42
    @14
    wa
    @2
    @36
    @31
    @40
    @0
    @14
    @2
    @36
    @31
    wi
    #
    wi
    #
    @0
    @14
    wa
    @40
    @15
    @44
    cA
    cz
    @1
    ssel2
    @40
    @15
    @2
    @43
    @5
    @1
    dvdsleabs
    3expia
    sylan2
    anassrs
    com23
    ralrimiva
    ancoms
    sylan2
    @37
    @39
    wa
    @36
    @38
    wa
    #
    vn
    cA
    wral
    @33
    @36
    @38
    vn
    cA
    r19.26
    @45
    @32
    vn
    cA
    @36
    @32
    pm3.35
    ralimi
    sylbir
    syl2anc
    ralrimiva
    @34
    @20
    @26
    wi
    #
    vw
    cA
    wral
    #
    vy
    cS
    wral
    @46
    vy
    cS
    wral
    #
    vw
    cA
    wral
    @29
    @33
    @47
    vy
    cS
    @32
    @46
    vn
    vw
    cA
    @1
    @19
    wceq
    #
    @2
    @20
    @31
    @26
    @22
    @49
    @30
    @25
    @5
    cle
    @1
    @19
    cabs
    fveq2
    breq2d
    imbi12d
    cbvralv
    ralbii
    @46
    vy
    vw
    cS
    cA
    ralcom
    @48
    @28
    vw
    cA
    @20
    @26
    vy
    cS
    r19.21v
    ralbii
    3bitri
    sylib
    @0
    @28
    @23
    vw
    cA
    @0
    @19
    cA
    wcel
    wa
    #
    @27
    @9
    @20
    @50
    @8
    @27
    vx
    @25
    cz
    @50
    @25
    @50
    @19
    cz
    wcel
    @25
    cn0
    wcel
    cA
    cz
    @19
    ssel2
    @19
    nn0abscl
    syl
    nn0zd
    @6
    @25
    wceq
    #
    @8
    @27
    wb
    @50
    @51
    @7
    @26
    vy
    cS
    @6
    @25
    @5
    cle
    breq2
    ralbidv
    adantl
    rspcedv
    imim2d
    ralimdva
    mpd
    @20
    @9
    vw
    cA
    r19.23v
    sylib
    imp
    sylan2b
    jca
end
