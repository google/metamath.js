include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "w3a.mm"
include "csn.mm"
include "cima.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "wa.mm"
include "cab.mm"
include "cabs.mm"
include "cfv.mm"
include "cmin.mm"
include "csqrt.mm"
include "cneg.mm"
include "cicc.mm"
include "c0.mm"
include "cif.mm"
include "copab.mm"
include "imaeq1i.mm"
include "cvv.mm"
include "wceq.mm"
include "vex.mm"
include "imasng.mm"
include "ax-mp.mm"
include "cop.mm"
include "df-br.mm"
include "weq.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "oveq2d.mm"
include "opelopab.mm"
include "anass.mm"
include "3bitri.mm"
include "abbii.mm"
include "3eqtri.mm"
include "simp3.mm"
include "biantrurd.mm"
include "abbidv.mm"
include "cxr.mm"
include "crab.mm"
include "resqcl.mm"
include "3ad2ant1.mm"
include "3ad2ant3.mm"
include "resubcld.mm"
include "adantr.mm"
include "absresq.mm"
include "recn.mm"
include "abscld.mm"
include "simp1.mm"
include "absge0d.mm"
include "simp2.mm"
include "le2sqd.mm"
include "subge0d.mm"
include "3bitr4d.mm"
include "biimpa.mm"
include "resqrtcld.mm"
include "renegcld.mm"
include "rexrd.mm"
include "iccval.mm"
include "syl2anc.mm"
include "iftrue.mm"
include "adantl.mm"
include "cc.mm"
include "recnd.mm"
include "sqsqrtd.mm"
include "breqan12rd.mm"
include "sqrtge0d.mm"
include "wb.mm"
include "leaddsub2d.mm"
include "adantlr.mm"
include "3bitr4rd.mm"
include "simpr.mm"
include "absled.mm"
include "rexr.mm"
include "3bitrd.mm"
include "pm5.32da.mm"
include "cmnf.mm"
include "clt.mm"
include "simprl.mm"
include "mnfxr.mm"
include "a1i.mm"
include "mnfltd.mm"
include "simprrl.mm"
include "xrltletrd.mm"
include "simprrr.mm"
include "xrre.mm"
include "syl22anc.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "bitr4d.mm"
include "df-rab.mm"
include "syl6eqr.mm"
include "3eqtr4rd.mm"
include "wn.mm"
include "ltnled.mm"
include "biimprd.mm"
include "imdistani.mm"
include "wral.mm"
include "readdcld.mm"
include "lt2sqd.mm"
include "breq2d.mm"
include "bitrd.mm"
include "3adant3.mm"
include "sqge0.mm"
include "addge01d.mm"
include "mpbid.mm"
include "ltletrd.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "syl5eqr.mm"
include "syl.mm"
include "iffalse.mm"
include "eqtr4d.mm"
include "pm2.61dan.mm"
include "eqtr3d.mm"
include "syl5eq.mm"

theorem areacirclem5
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cR: class R
  let cS: class S
  let vu: setvar u
  let vv: setvar v
  assume areacirc.1: |- S = { <. x , y >. | ( ( x e. RR /\ y e. RR ) /\ ( ( x ^ 2 ) + ( y ^ 2 ) ) <_ ( R ^ 2 ) ) }

  disjoint x y
  disjoint t x
  disjoint R x
  disjoint t y
  disjoint R y
  disjoint R t
  disjoint S t
  disjoint u x
  disjoint v x
  disjoint u y
  disjoint v y
  disjoint t u
  disjoint t v
  disjoint u v
  disjoint R u
  disjoint R v
  disjoint S u
  disjoint S v
  assert |- ( ( R e. RR /\ 0 <_ R /\ t e. RR ) -> ( S " { t } ) = if ( ( abs ` t ) <_ R , ( -u ( sqrt ` ( ( R ^ 2 ) - ( t ^ 2 ) ) ) [,] ( sqrt ` ( ( R ^ 2 ) - ( t ^ 2 ) ) ) ) , (/) ) )

  proof
    cR
    cr
    wcel
    #
    cc0
    cR
    cle
    wbr
    #
    vt
    cv
    #
    cr
    wcel
    #
    w3a
    #
    cS
    @2
    csn
    #
    cima
    #
    @3
    vu
    cv
    #
    cr
    wcel
    #
    @2
    c2
    cexp
    co
    #
    @7
    c2
    cexp
    co
    #
    caddc
    co
    #
    cR
    c2
    cexp
    co
    #
    cle
    wbr
    #
    wa
    #
    wa
    #
    vu
    cab
    #
    @2
    cabs
    cfv
    #
    cR
    cle
    wbr
    #
    @12
    @9
    cmin
    co
    #
    csqrt
    cfv
    #
    cneg
    #
    @20
    cicc
    co
    #
    c0
    cif
    #
    @6
    vx
    cv
    #
    cr
    wcel
    #
    vy
    cv
    #
    cr
    wcel
    #
    wa
    #
    @24
    c2
    cexp
    co
    #
    @26
    c2
    cexp
    co
    #
    caddc
    co
    #
    @12
    cle
    wbr
    #
    wa
    #
    vx
    vy
    copab
    #
    @5
    cima
    #
    @2
    @7
    @34
    wbr
    #
    vu
    cab
    #
    @16
    cS
    @34
    @5
    areacirc.1
    imaeq1i
    @2
    cvv
    wcel
    @35
    @37
    wceq
    vt
    vex
    #
    vu
    @2
    cvv
    @34
    imasng
    ax-mp
    @36
    @15
    vu
    @36
    @2
    @7
    cop
    @34
    wcel
    @3
    @8
    wa
    #
    @13
    wa
    #
    @15
    @2
    @7
    @34
    df-br
    @33
    @3
    @27
    wa
    #
    @9
    @30
    caddc
    co
    #
    @12
    cle
    wbr
    #
    wa
    @40
    vx
    vy
    @2
    @7
    @38
    vu
    vex
    vx
    vt
    weq
    #
    @28
    @41
    @32
    @43
    @44
    @25
    @3
    @27
    @24
    @2
    cr
    eleq1
    anbi1d
    @44
    @31
    @42
    @12
    cle
    @44
    @29
    @9
    @30
    caddc
    @24
    @2
    c2
    cexp
    oveq1
    oveq1d
    breq1d
    anbi12d
    vy
    vu
    weq
    #
    @41
    @39
    @43
    @13
    @45
    @27
    @8
    @3
    @26
    @7
    cr
    eleq1
    anbi2d
    @45
    @42
    @11
    @12
    cle
    @45
    @30
    @10
    @9
    caddc
    @26
    @7
    c2
    cexp
    oveq1
    oveq2d
    breq1d
    anbi12d
    opelopab
    @3
    @8
    @13
    anass
    3bitri
    abbii
    3eqtri
    @4
    @14
    vu
    cab
    #
    @16
    @23
    @4
    @14
    @15
    vu
    @4
    @3
    @14
    @0
    @1
    @3
    simp3
    biantrurd
    abbidv
    @4
    @18
    @46
    @23
    wceq
    @4
    @18
    wa
    #
    @22
    @21
    @7
    cle
    wbr
    #
    @7
    @20
    cle
    wbr
    #
    wa
    #
    vu
    cxr
    crab
    #
    @23
    @46
    @47
    @21
    cxr
    wcel
    @20
    cxr
    wcel
    @22
    @51
    wceq
    @47
    @21
    @47
    @20
    @47
    @19
    @4
    @19
    cr
    wcel
    @18
    @4
    @12
    @9
    @0
    @1
    @12
    cr
    wcel
    #
    @3
    cR
    resqcl
    3ad2ant1
    #
    @3
    @0
    @9
    cr
    wcel
    #
    @1
    @2
    resqcl
    3ad2ant3
    #
    resubcld
    #
    adantr
    #
    @4
    @18
    cc0
    @19
    cle
    wbr
    #
    @4
    @17
    c2
    cexp
    co
    #
    @12
    cle
    wbr
    @9
    @12
    cle
    wbr
    @18
    @58
    @4
    @59
    @9
    @12
    cle
    @3
    @0
    @59
    @9
    wceq
    @1
    @2
    absresq
    3ad2ant3
    #
    breq1d
    @4
    @17
    cR
    @3
    @0
    @17
    cr
    wcel
    @1
    @3
    @2
    @2
    recn
    #
    abscld
    3ad2ant3
    #
    @0
    @1
    @3
    simp1
    #
    @3
    @0
    cc0
    @17
    cle
    wbr
    @1
    @3
    @2
    @61
    absge0d
    3ad2ant3
    #
    @0
    @1
    @3
    simp2
    #
    le2sqd
    @4
    @12
    @9
    @53
    @55
    subge0d
    3bitr4d
    biimpa
    #
    resqrtcld
    #
    renegcld
    #
    rexrd
    @47
    @20
    @67
    rexrd
    vu
    @21
    @20
    iccval
    syl2anc
    @18
    @23
    @22
    wceq
    @4
    @18
    @22
    c0
    iftrue
    adantl
    @47
    @46
    @7
    cxr
    wcel
    #
    @50
    wa
    #
    vu
    cab
    @51
    @47
    @14
    @70
    vu
    @47
    @14
    @8
    @70
    wa
    @70
    @47
    @8
    @13
    @70
    @47
    @8
    wa
    #
    @13
    @7
    cabs
    cfv
    #
    @20
    cle
    wbr
    #
    @50
    @70
    @71
    @72
    c2
    cexp
    co
    #
    @20
    c2
    cexp
    co
    #
    cle
    wbr
    @10
    @19
    cle
    wbr
    #
    @73
    @13
    @8
    @47
    @74
    @10
    @75
    @19
    cle
    @7
    absresq
    @47
    @19
    @4
    @19
    cc
    wcel
    @18
    @4
    @19
    @56
    recnd
    adantr
    sqsqrtd
    breqan12rd
    @71
    @72
    @20
    @8
    @72
    cr
    wcel
    @47
    @8
    @7
    @7
    recn
    #
    abscld
    adantl
    @47
    @20
    cr
    wcel
    #
    @8
    @67
    adantr
    #
    @8
    cc0
    @72
    cle
    wbr
    @47
    @8
    @7
    @77
    absge0d
    adantl
    @47
    cc0
    @20
    cle
    wbr
    @8
    @47
    @19
    @57
    @66
    sqrtge0d
    adantr
    le2sqd
    @4
    @8
    @13
    @76
    wb
    @18
    @4
    @8
    wa
    @9
    @10
    @12
    @4
    @54
    @8
    @55
    adantr
    @8
    @10
    cr
    wcel
    #
    @4
    @7
    resqcl
    #
    adantl
    @4
    @52
    @8
    @53
    adantr
    leaddsub2d
    adantlr
    3bitr4rd
    @71
    @7
    @20
    @47
    @8
    simpr
    @79
    absled
    @71
    @69
    @50
    @8
    @69
    @47
    @7
    rexr
    adantl
    biantrurd
    3bitrd
    pm5.32da
    @47
    @70
    @8
    @47
    @70
    @8
    @47
    @70
    wa
    #
    @69
    @78
    cmnf
    @7
    clt
    wbr
    @49
    @8
    @47
    @69
    @50
    simprl
    #
    @47
    @78
    @70
    @67
    adantr
    @82
    cmnf
    @21
    @7
    cmnf
    cxr
    wcel
    @82
    mnfxr
    a1i
    @82
    @21
    @47
    @21
    cr
    wcel
    @70
    @68
    adantr
    rexrd
    @83
    @47
    cmnf
    @21
    clt
    wbr
    @70
    @47
    @21
    @68
    mnfltd
    adantr
    @47
    @69
    @48
    @49
    simprrl
    xrltletrd
    @47
    @69
    @48
    @49
    simprrr
    @7
    @20
    xrre
    syl22anc
    ex
    pm4.71rd
    bitr4d
    abbidv
    @50
    vu
    cxr
    df-rab
    syl6eqr
    3eqtr4rd
    @4
    @18
    wn
    #
    wa
    #
    @46
    c0
    @23
    @85
    @4
    cR
    @17
    clt
    wbr
    #
    wa
    #
    @46
    c0
    wceq
    @4
    @84
    @86
    @4
    @86
    @84
    @4
    cR
    @17
    @63
    @62
    ltnled
    biimprd
    imdistani
    @87
    @46
    @13
    vu
    cr
    crab
    #
    c0
    @13
    vu
    cr
    df-rab
    @87
    @13
    wn
    #
    vu
    cr
    wral
    @88
    c0
    wceq
    @87
    @89
    vu
    cr
    @4
    @86
    @8
    @89
    @4
    @86
    @8
    w3a
    #
    @12
    @11
    clt
    wbr
    @89
    @90
    @12
    @9
    @11
    @4
    @86
    @52
    @8
    @53
    3ad2ant1
    #
    @4
    @86
    @54
    @8
    @55
    3ad2ant1
    #
    @90
    @9
    @10
    @92
    @8
    @4
    @80
    @86
    @81
    3ad2ant3
    #
    readdcld
    #
    @4
    @86
    @12
    @9
    clt
    wbr
    #
    @8
    @4
    @86
    @95
    @4
    @86
    @12
    @59
    clt
    wbr
    @95
    @4
    cR
    @17
    @63
    @62
    @65
    @64
    lt2sqd
    @4
    @59
    @9
    @12
    clt
    @60
    breq2d
    bitrd
    biimpa
    3adant3
    @90
    cc0
    @10
    cle
    wbr
    #
    @9
    @11
    cle
    wbr
    @8
    @4
    @96
    @86
    @7
    sqge0
    3ad2ant3
    @90
    @9
    @10
    @92
    @93
    addge01d
    mpbid
    ltletrd
    @90
    @12
    @11
    @91
    @94
    ltnled
    mpbid
    3expa
    ralrimiva
    @13
    vu
    cr
    rabeq0
    sylibr
    syl5eqr
    syl
    @84
    @23
    c0
    wceq
    @4
    @18
    @22
    c0
    iffalse
    adantl
    eqtr4d
    pm2.61dan
    eqtr3d
    syl5eq
end
