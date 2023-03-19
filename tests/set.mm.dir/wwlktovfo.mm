include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "wwlktovf.mm"
include "a1i.mm"
include "cpr.mm"
include "wa.mm"
include "weq.mm"
include "preq2.mm"
include "eleq1d.mm"
include "elrab2.mm"
include "c1.mm"
include "chash.mm"
include "c2.mm"
include "cc0.mm"
include "w3a.mm"
include "cword.mm"
include "crab.mm"
include "wex.mm"
include "cop.mm"
include "simpl.mm"
include "anim2i.mm"
include "eqidd.mm"
include "wrdlen2i.mm"
include "sylc.mm"
include "cvv.mm"
include "prex.mm"
include "wi.mm"
include "eleq1.mm"
include "biimpd.mm"
include "adantr.mm"
include "com12.mm"
include "impcom.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "adantl.mm"
include "fveq1.mm"
include "anbi12d.mm"
include "preq12.mm"
include "eqcomd.mm"
include "syl6bi.mm"
include "com13.mm"
include "ad2antll.mm"
include "imp.mm"
include "3jca.mm"
include "eqcom.mm"
include "eqeq2d.mm"
include "syl5bi.mm"
include "jca31.mm"
include "exp31.mm"
include "eqcoms.mm"
include "spcimedv.mm"
include "mpd.mm"
include "preq12d.mm"
include "3anbi123d.mm"
include "elrab.mm"
include "anbi1i.mm"
include "exbii.mm"
include "sylibr.mm"
include "df-rex.mm"
include "rexeqi.mm"
include "fvex.mm"
include "fvmpt.mm"
include "rexbiia.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "sylanbrc.mm"

theorem wwlktovfo
  let vw: setvar w
  let vt: setvar t
  let cD: class D
  let cP: class P
  let cR: class R
  let vn: setvar n
  let cF: class F
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vi: setvar i
  let vp: setvar p
  let vu: setvar u
  assume wrd2f1tovbij.d: |- D = { w e. Word V | ( ( # ` w ) = 2 /\ ( w ` 0 ) = P /\ { ( w ` 0 ) , ( w ` 1 ) } e. X ) }
  assume wrd2f1tovbij.r: |- R = { n e. V | { P , n } e. X }
  assume wrd2f1tovbij.f: |- F = ( t e. D |-> ( t ` 1 ) )

  disjoint D t
  disjoint P n
  disjoint P t
  disjoint P w
  disjoint n t
  disjoint n w
  disjoint t w
  disjoint R t
  disjoint V n
  disjoint V t
  disjoint V w
  disjoint X n
  disjoint X w
  disjoint D x
  disjoint D y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint P x
  disjoint P y
  disjoint t x
  disjoint t y
  disjoint w x
  disjoint w y
  disjoint V x
  disjoint V y
  disjoint i x
  disjoint i y
  disjoint D p
  disjoint D u
  disjoint p u
  disjoint F u
  disjoint F p
  disjoint P p
  disjoint P u
  disjoint R p
  disjoint R u
  disjoint V p
  disjoint V u
  disjoint X u
  disjoint n p
  disjoint t u
  disjoint u w
  assert |- ( P e. V -> F : D -onto-> R )

  proof
    cP
    cV
    wcel
    #
    cD
    cR
    cF
    wf
    #
    vp
    cv
    #
    vu
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vu
    cD
    wrex
    #
    vp
    cR
    wral
    cD
    cR
    cF
    wfo
    @1
    @0
    vw
    vt
    cD
    cP
    cR
    vn
    cF
    cV
    cX
    wrd2f1tovbij.d
    wrd2f1tovbij.r
    wrd2f1tovbij.f
    wwlktovf
    a1i
    @0
    @6
    vp
    cR
    @2
    cR
    wcel
    @0
    @2
    cV
    wcel
    #
    cP
    @2
    cpr
    #
    cX
    wcel
    #
    wa
    #
    @6
    cP
    vn
    cv
    #
    cpr
    #
    cX
    wcel
    @9
    vn
    @2
    cV
    cR
    vn
    vp
    weq
    @12
    @8
    cX
    @11
    @2
    cP
    preq2
    eleq1d
    wrd2f1tovbij.r
    elrab2
    @0
    @10
    wa
    #
    @2
    c1
    @3
    cfv
    #
    wceq
    #
    vu
    cD
    wrex
    #
    @6
    @13
    @15
    vu
    vw
    cv
    #
    chash
    cfv
    #
    c2
    wceq
    #
    cc0
    @17
    cfv
    #
    cP
    wceq
    #
    @20
    c1
    @17
    cfv
    #
    cpr
    #
    cX
    wcel
    #
    w3a
    #
    vw
    cV
    cword
    #
    crab
    #
    wrex
    #
    @16
    @13
    @3
    @27
    wcel
    #
    @15
    wa
    #
    vu
    wex
    #
    @28
    @13
    @3
    @26
    wcel
    #
    @3
    chash
    cfv
    #
    c2
    wceq
    #
    cc0
    @3
    cfv
    #
    cP
    wceq
    #
    @35
    @14
    cpr
    #
    cX
    wcel
    #
    w3a
    #
    wa
    #
    @15
    wa
    #
    vu
    wex
    #
    @31
    @13
    cc0
    cP
    cop
    #
    c1
    @2
    cop
    #
    cpr
    #
    @26
    wcel
    #
    @45
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    #
    cc0
    @45
    cfv
    #
    cP
    wceq
    #
    c1
    @45
    cfv
    #
    @2
    wceq
    #
    wa
    #
    wa
    #
    @42
    @13
    @0
    @7
    wa
    @45
    @45
    wceq
    @55
    @10
    @7
    @0
    @7
    @9
    simpl
    anim2i
    @13
    @45
    eqidd
    cP
    @2
    cV
    @45
    wrdlen2i
    sylc
    @13
    @41
    @55
    vu
    @45
    cvv
    @45
    cvv
    wcel
    @13
    @43
    @44
    prex
    a1i
    @3
    @45
    wceq
    @13
    @55
    @41
    wi
    #
    @13
    @56
    wi
    @45
    @3
    @45
    @3
    wceq
    #
    @13
    @55
    @41
    @57
    @13
    wa
    #
    @55
    wa
    #
    @32
    @39
    @15
    @55
    @58
    @32
    @49
    @58
    @32
    wi
    #
    @54
    @46
    @60
    @48
    @58
    @46
    @32
    @57
    @46
    @32
    wi
    @13
    @57
    @46
    @32
    @45
    @3
    @26
    eleq1
    biimpd
    adantr
    com12
    adantr
    adantr
    impcom
    @59
    @34
    @36
    @38
    @55
    @58
    @34
    @49
    @58
    @34
    wi
    #
    @54
    @48
    @61
    @46
    @58
    @48
    @34
    @57
    @48
    @34
    wi
    @13
    @57
    @48
    @34
    @57
    @47
    @33
    c2
    @45
    @3
    chash
    fveq2
    eqeq1d
    biimpd
    adantr
    com12
    adantl
    adantr
    impcom
    @55
    @58
    @36
    @54
    @58
    @36
    wi
    #
    @49
    @51
    @62
    @53
    @58
    @51
    @36
    @57
    @51
    @36
    wi
    @13
    @57
    @51
    @36
    @57
    @50
    @35
    cP
    cc0
    @45
    @3
    fveq1
    eqeq1d
    #
    biimpd
    adantr
    com12
    adantr
    adantl
    impcom
    @58
    @55
    @38
    @13
    @57
    @55
    @38
    wi
    #
    @9
    @57
    @64
    wi
    @0
    @7
    @55
    @57
    @9
    @38
    @54
    @57
    @9
    @38
    wi
    #
    wi
    @49
    @57
    @54
    @65
    @57
    @54
    @36
    @14
    @2
    wceq
    #
    wa
    #
    @65
    @57
    @51
    @36
    @53
    @66
    @63
    @57
    @52
    @14
    @2
    c1
    @45
    @3
    fveq1
    #
    eqeq1d
    anbi12d
    @67
    @9
    @38
    @67
    @8
    @37
    cX
    @67
    @37
    @8
    @35
    @14
    cP
    @2
    preq12
    eqcomd
    eleq1d
    biimpd
    syl6bi
    com12
    adantl
    com13
    ad2antll
    impcom
    imp
    3jca
    @58
    @55
    @15
    @57
    @55
    @15
    wi
    @13
    @55
    @57
    @15
    @53
    @57
    @15
    wi
    @49
    @51
    @57
    @53
    @15
    @53
    @2
    @52
    wceq
    #
    @57
    @15
    @52
    @2
    eqcom
    @57
    @69
    @15
    @57
    @52
    @14
    @2
    @68
    eqeq2d
    biimpd
    syl5bi
    com12
    ad2antll
    com12
    adantr
    imp
    jca31
    exp31
    eqcoms
    impcom
    spcimedv
    mpd
    @30
    @41
    vu
    @29
    @40
    @15
    @25
    @39
    vw
    @3
    @26
    vw
    vu
    weq
    #
    @19
    @34
    @21
    @36
    @24
    @38
    @70
    @18
    @33
    c2
    @17
    @3
    chash
    fveq2
    eqeq1d
    @70
    @20
    @35
    cP
    cc0
    @17
    @3
    fveq1
    #
    eqeq1d
    @70
    @23
    @37
    cX
    @70
    @20
    @35
    @22
    @14
    @71
    c1
    @17
    @3
    fveq1
    preq12d
    eleq1d
    3anbi123d
    elrab
    anbi1i
    exbii
    sylibr
    @15
    vu
    @27
    df-rex
    sylibr
    @15
    vu
    cD
    @27
    wrd2f1tovbij.d
    rexeqi
    sylibr
    @5
    @15
    vu
    cD
    @3
    cD
    wcel
    @4
    @14
    @2
    vt
    @3
    c1
    vt
    cv
    #
    cfv
    @14
    cD
    cF
    c1
    @72
    @3
    fveq1
    wrd2f1tovbij.f
    c1
    @3
    fvex
    fvmpt
    eqeq2d
    rexbiia
    sylibr
    sylan2b
    ralrimiva
    vu
    vp
    cD
    cR
    cF
    dffo3
    sylanbrc
end
