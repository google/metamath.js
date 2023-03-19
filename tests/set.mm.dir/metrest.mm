include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "cbl.mm"
include "crp.mm"
include "wral.mm"
include "inss1.mm"
include "elmopn2.mm"
include "simplbda.mm"
include "adantlr.mm"
include "ssralv.mm"
include "mpsyl.mm"
include "ssrin.mm"
include "reximi.mm"
include "ralimi.mm"
include "syl.mm"
include "inss2.mm"
include "jctil.mm"
include "sseq1.mm"
include "sseq2.mm"
include "rexbidv.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "cab.mm"
include "cuni.mm"
include "ctop.mm"
include "mopntop.mm"
include "ad2antrr.mm"
include "wi.mm"
include "wel.mm"
include "ssel2.mm"
include "cxr.mm"
include "rpxr.mm"
include "w3a.mm"
include "blopn.mm"
include "eleq1a.mm"
include "3expa.mm"
include "sylan2.mm"
include "anassrs.mm"
include "adantrd.mm"
include "adantrr.mm"
include "abssdv.mm"
include "uniopn.mm"
include "syl2anc.mm"
include "oveq1.mm"
include "ineq1d.mm"
include "sseq1d.mm"
include "rspccv.mm"
include "ad2antll.mm"
include "ssel.mm"
include "blcntr.mm"
include "a1d.mm"
include "ancld.mm"
include "reximdva.mm"
include "ex.mm"
include "sylan9r.mm"
include "mpdd.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "sylcom.mm"
include "simprl.mm"
include "sseld.mm"
include "jcad.mm"
include "elin.mm"
include "sylan2br.mm"
include "expr.mm"
include "rexlimivw.mm"
include "imp.mm"
include "impbid1.mm"
include "wex.mm"
include "eluniab.mm"
include "ancom.mm"
include "anass.mm"
include "r19.41v.mm"
include "rexbii.mm"
include "bitr2i.mm"
include "3bitri.mm"
include "exbii.mm"
include "ovex.mm"
include "ineq1.mm"
include "eleq2.mm"
include "ceqsexv.mm"
include "rexcom4.mm"
include "bitr3i.mm"
include "anbi1i.mm"
include "syl6bb.mm"
include "eqrdv.mm"
include "eqeq2d.mm"
include "impbid.mm"
include "wb.mm"
include "simpr.mm"
include "elind.mm"
include "blres.mm"
include "rexbidva.mm"
include "ralbidva.mm"
include "pm5.32da.mm"
include "bitr4d.mm"
include "cvv.mm"
include "adantr.mm"
include "id.mm"
include "mopnm.mm"
include "ssexg.mm"
include "syl2anr.mm"
include "elrest.mm"
include "cxp.mm"
include "cres.mm"
include "xmetres2.mm"
include "syl5eqel.mm"
include "3bitr4d.mm"

theorem metrest
  let cC: class C
  let cD: class D
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume metrest.1: |- D = ( C |` ( Y X. Y ) )
  assume metrest.3: |- J = ( MetOpen ` C )
  assume metrest.4: |- K = ( MetOpen ` D )


  assert |- ( ( C e. ( *Met ` X ) /\ Y C_ X ) -> ( J |`t Y ) = K )

  proof
    cC
    cX
    cxmt
    cfv
    wcel
    #
    cY
    cX
    wss
    #
    wa
    #
    vx
    cJ
    cY
    crest
    co
    #
    cK
    @2
    vx
    cv
    #
    vu
    cv
    #
    cY
    cin
    #
    wceq
    #
    vu
    cJ
    wrex
    #
    @4
    cY
    wss
    #
    vy
    cv
    #
    vr
    cv
    #
    cD
    cbl
    cfv
    co
    #
    @4
    wss
    #
    vr
    crp
    wrex
    #
    vy
    @4
    wral
    #
    wa
    #
    @4
    @3
    wcel
    #
    @4
    cK
    wcel
    #
    @2
    @8
    @9
    @10
    @11
    cC
    cbl
    cfv
    #
    co
    #
    cY
    cin
    #
    @4
    wss
    #
    vr
    crp
    wrex
    #
    vy
    @4
    wral
    #
    wa
    #
    @16
    @2
    @8
    @25
    @2
    @7
    @25
    vu
    cJ
    @2
    @5
    cJ
    wcel
    #
    wa
    #
    @25
    @7
    @6
    cY
    wss
    #
    @21
    @6
    wss
    #
    vr
    crp
    wrex
    #
    vy
    @6
    wral
    #
    wa
    @27
    @31
    @28
    @27
    @20
    @5
    wss
    #
    vr
    crp
    wrex
    #
    vy
    @6
    wral
    #
    @31
    @6
    @5
    wss
    @27
    @33
    vy
    @5
    wral
    #
    @34
    @5
    cY
    inss1
    @0
    @26
    @35
    @1
    @0
    @26
    @5
    cX
    wss
    @35
    vy
    vr
    @5
    cC
    cJ
    cX
    metrest.3
    elmopn2
    simplbda
    adantlr
    @33
    vy
    @6
    @5
    ssralv
    mpsyl
    @33
    @30
    vy
    @6
    @32
    @29
    vr
    crp
    @20
    @5
    cY
    ssrin
    reximi
    ralimi
    syl
    @5
    cY
    inss2
    jctil
    @7
    @9
    @28
    @24
    @31
    @4
    @6
    cY
    sseq1
    @23
    @30
    vy
    @4
    @6
    @7
    @22
    @29
    vr
    crp
    @4
    @6
    @21
    sseq2
    rexbidv
    raleqbi1dv
    anbi12d
    syl5ibrcom
    rexlimdva
    @2
    @25
    @8
    @2
    @25
    wa
    #
    vz
    cv
    #
    @20
    wceq
    #
    vr
    crp
    wrex
    #
    vy
    @4
    wrex
    #
    @37
    cY
    cin
    #
    @4
    wss
    #
    wa
    #
    vz
    cab
    #
    cuni
    #
    cJ
    wcel
    #
    @4
    @45
    cY
    cin
    #
    wceq
    #
    @8
    @36
    cJ
    ctop
    wcel
    #
    @44
    cJ
    wss
    @46
    @0
    @49
    @1
    @25
    cC
    cJ
    cX
    metrest.3
    mopntop
    #
    ad2antrr
    @36
    @43
    vz
    cJ
    @2
    @9
    @43
    @37
    cJ
    wcel
    #
    wi
    @24
    @2
    @9
    wa
    #
    @40
    @51
    @42
    @52
    @39
    @51
    vy
    @4
    @2
    @9
    vy
    vx
    wel
    #
    @39
    @51
    wi
    #
    @9
    @53
    wa
    #
    @2
    @10
    cY
    wcel
    #
    @54
    @4
    cY
    @10
    ssel2
    #
    @0
    @1
    @56
    @54
    @1
    @56
    wa
    #
    @0
    @10
    cX
    wcel
    #
    @54
    cY
    cX
    @10
    ssel2
    #
    @0
    @59
    wa
    #
    @38
    @51
    vr
    crp
    @11
    crp
    wcel
    #
    @61
    @11
    cxr
    wcel
    #
    @38
    @51
    wi
    #
    @11
    rpxr
    #
    @0
    @59
    @63
    @64
    @0
    @59
    @63
    w3a
    @20
    cJ
    wcel
    @64
    cC
    @10
    @11
    cJ
    cX
    metrest.3
    blopn
    @20
    cJ
    @37
    eleq1a
    syl
    3expa
    sylan2
    rexlimdva
    sylan2
    anassrs
    sylan2
    anassrs
    rexlimdva
    adantrd
    adantrr
    abssdv
    @44
    cJ
    uniopn
    syl2anc
    @36
    vu
    @4
    @47
    @36
    vu
    vx
    wel
    #
    @22
    @5
    @20
    wcel
    #
    wa
    #
    vr
    crp
    wrex
    #
    vy
    @4
    wrex
    #
    @5
    cY
    wcel
    #
    wa
    #
    @5
    @47
    wcel
    #
    @36
    @66
    @72
    @36
    @66
    @70
    @71
    @36
    @66
    @5
    @11
    @19
    co
    #
    cY
    cin
    #
    @4
    wss
    #
    @5
    @74
    wcel
    #
    wa
    #
    vr
    crp
    wrex
    #
    @70
    @36
    @66
    @76
    vr
    crp
    wrex
    #
    @79
    @24
    @66
    @80
    wi
    @2
    @9
    @23
    @80
    vy
    @5
    @4
    @10
    @5
    wceq
    #
    @22
    @76
    vr
    crp
    @81
    @21
    @75
    @4
    @81
    @20
    @74
    cY
    @10
    @5
    @11
    @19
    oveq1
    #
    ineq1d
    sseq1d
    #
    rexbidv
    rspccv
    ad2antll
    @2
    @9
    @66
    @80
    @79
    wi
    #
    wi
    @24
    @9
    @66
    @71
    @2
    @84
    @4
    cY
    @5
    ssel
    @1
    @71
    @5
    cX
    wcel
    #
    @0
    @84
    cY
    cX
    @5
    ssel
    @0
    @85
    @84
    @0
    @85
    wa
    @76
    @78
    vr
    crp
    @0
    @85
    @62
    @76
    @78
    wi
    @0
    @85
    @62
    w3a
    #
    @76
    @77
    @86
    @77
    @76
    cC
    @5
    @11
    cX
    blcntr
    a1d
    ancld
    3expa
    reximdva
    ex
    sylan9r
    sylan9r
    adantrr
    mpdd
    @66
    @79
    @70
    @69
    @79
    vy
    @5
    @4
    @81
    @68
    @78
    vr
    crp
    @81
    @22
    @76
    @67
    @77
    @83
    @81
    @20
    @74
    @5
    @82
    eleq2d
    anbi12d
    rexbidv
    rspcev
    ex
    sylcom
    @36
    @4
    cY
    @5
    @2
    @9
    @24
    simprl
    sseld
    jcad
    @70
    @71
    @66
    @69
    @71
    @66
    wi
    #
    vy
    @4
    @68
    @87
    vr
    crp
    @22
    @67
    @71
    @66
    @67
    @71
    wa
    @22
    @5
    @21
    wcel
    @66
    @5
    @20
    cY
    elin
    @21
    @4
    @5
    ssel2
    sylan2br
    expr
    rexlimivw
    rexlimivw
    imp
    impbid1
    @73
    @5
    @45
    wcel
    #
    @71
    wa
    @72
    @5
    @45
    cY
    elin
    @88
    @70
    @71
    @88
    vu
    vz
    wel
    #
    @43
    wa
    #
    vz
    wex
    @38
    @42
    @89
    wa
    #
    wa
    #
    vr
    crp
    wrex
    #
    vy
    @4
    wrex
    #
    vz
    wex
    #
    @70
    @43
    vz
    @5
    eluniab
    @90
    @94
    vz
    @90
    @43
    @89
    wa
    @40
    @91
    wa
    #
    @94
    @89
    @43
    ancom
    @40
    @42
    @89
    anass
    @94
    @39
    @91
    wa
    #
    vy
    @4
    wrex
    @96
    @93
    @97
    vy
    @4
    @38
    @91
    vr
    crp
    r19.41v
    rexbii
    @39
    @91
    vy
    @4
    r19.41v
    bitr2i
    3bitri
    exbii
    @70
    @93
    vz
    wex
    #
    vy
    @4
    wrex
    @95
    @69
    @98
    vy
    @4
    @69
    @92
    vz
    wex
    #
    vr
    crp
    wrex
    @98
    @99
    @68
    vr
    crp
    @91
    @68
    vz
    @20
    @10
    @11
    @19
    ovex
    @38
    @42
    @22
    @89
    @67
    @38
    @41
    @21
    @4
    @37
    @20
    cY
    ineq1
    sseq1d
    @37
    @20
    @5
    eleq2
    anbi12d
    ceqsexv
    rexbii
    @92
    vr
    vz
    crp
    rexcom4
    bitr3i
    rexbii
    @93
    vy
    vz
    @4
    rexcom4
    bitr2i
    3bitri
    anbi1i
    bitr2i
    syl6bb
    eqrdv
    @7
    @48
    vu
    @45
    cJ
    @5
    @45
    wceq
    @6
    @47
    @4
    @5
    @45
    cY
    ineq1
    eqeq2d
    rspcev
    syl2anc
    ex
    impbid
    @2
    @9
    @15
    @24
    @52
    @14
    @23
    vy
    @4
    @2
    @9
    @53
    @14
    @23
    wb
    #
    @55
    @2
    @56
    @100
    @57
    @0
    @1
    @56
    @100
    @58
    @0
    @10
    cX
    cY
    cin
    wcel
    #
    @100
    @58
    cX
    cY
    @10
    @60
    @1
    @56
    simpr
    elind
    @0
    @101
    wa
    #
    @13
    @22
    vr
    crp
    @62
    @102
    @63
    @13
    @22
    wb
    #
    @65
    @0
    @101
    @63
    @103
    @0
    @101
    @63
    w3a
    @12
    @21
    @4
    cD
    cC
    @10
    @11
    cX
    cY
    metrest.1
    blres
    sseq1d
    3expa
    sylan2
    rexbidva
    sylan2
    anassrs
    sylan2
    anassrs
    ralbidva
    pm5.32da
    bitr4d
    @2
    @49
    cY
    cvv
    wcel
    #
    @17
    @8
    wb
    @0
    @49
    @1
    @50
    adantr
    @1
    @1
    cX
    cJ
    wcel
    @104
    @0
    @1
    id
    cC
    cJ
    cX
    metrest.3
    mopnm
    cY
    cX
    cJ
    ssexg
    syl2anr
    vu
    @4
    cY
    cJ
    ctop
    cvv
    elrest
    syl2anc
    @2
    cD
    cY
    cxmt
    cfv
    #
    wcel
    @18
    @16
    wb
    @2
    cD
    cC
    cY
    cY
    cxp
    cres
    @105
    metrest.1
    cC
    cY
    cX
    xmetres2
    syl5eqel
    vy
    vr
    @4
    cD
    cK
    cY
    metrest.4
    elmopn2
    syl
    3bitr4d
    eqrdv
end
