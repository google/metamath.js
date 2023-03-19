include "cxr.mm"
include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wtru.mm"
include "cvv.mm"
include "xrex.mm"
include "a1i.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cxne.mm"
include "cxad.mm"
include "co.mm"
include "cif.mm"
include "wral.mm"
include "wa.mm"
include "id.mm"
include "xnegcl.mm"
include "xaddcl.mm"
include "syl2anr.mm"
include "sylan2.mm"
include "ifcld.mm"
include "rgen2a.mm"
include "xrsds.mm"
include "fmpt2.mm"
include "mpbi.mm"
include "cc0.mm"
include "breq2.mm"
include "wb.mm"
include "xsubge0.mm"
include "ancoms.mm"
include "biimpar.mm"
include "wn.mm"
include "xrletri.mm"
include "orcanai.mm"
include "syldan.mm"
include "ifbothda.mm"
include "xrsdsval.mm"
include "breqtrrd.mm"
include "adantl.mm"
include "weq.mm"
include "wceq.mm"
include "biantrud.mm"
include "eqeltrd.mm"
include "0xr.mm"
include "xrletri3.mm"
include "sylancl.mm"
include "simpr.mm"
include "wne.mm"
include "cr.mm"
include "simplr.mm"
include "0re.mm"
include "syl6eqel.mm"
include "xrsdsreclb.mm"
include "3expa.mm"
include "adantlr.mm"
include "mpbid.mm"
include "simpld.mm"
include "recnd.mm"
include "simprd.mm"
include "cmin.mm"
include "rexsub.mm"
include "syl.mm"
include "eqeq1d.mm"
include "biimpa.mm"
include "adantr.mm"
include "xneg11.mm"
include "xnegdi.mm"
include "syl2anc.mm"
include "xnegneg.mm"
include "oveq2d.mm"
include "simpl.mm"
include "xaddcom.mm"
include "3eqtrd.mm"
include "xneg0.mm"
include "eqeq12d.mm"
include "bitr3d.mm"
include "ad2antrr.mm"
include "biidd.mm"
include "eqeq1.mm"
include "bibi1d.mm"
include "ifboth.mm"
include "eqtr3d.mm"
include "subeq0d.mm"
include "pm2.61dane.mm"
include "ex.mm"
include "anidms.mm"
include "xrleid.mm"
include "iftrued.mm"
include "xnegid.mm"
include "oveq1.mm"
include "syl5ibrcom.mm"
include "impbid.mm"
include "3bitr2d.mm"
include "w3a.mm"
include "caddc.mm"
include "simplrr.mm"
include "leidd.mm"
include "oveq1d.mm"
include "simpll1.mm"
include "oveq12.mm"
include "vtoclga.mm"
include "eqtrd.mm"
include "addid2d.mm"
include "eqtr2d.mm"
include "3brtr3d.mm"
include "simplrl.mm"
include "eqeltrrd.mm"
include "simpll2.mm"
include "oveq2.mm"
include "eqtr4d.mm"
include "eqeq2.mm"
include "clt.mm"
include "wo.mm"
include "xrleloe.mm"
include "neneqd.mm"
include "biorf.mm"
include "orcom.mm"
include "syl6bb.mm"
include "xrltnle.mm"
include "con2bid.mm"
include "iffalsed.mm"
include "3eqtr4d.mm"
include "oveq12d.mm"
include "addid1d.mm"
include "3brtr4d.mm"
include "cabs.mm"
include "simpll3.mm"
include "simprl.mm"
include "syl3anc.mm"
include "simprr.mm"
include "abs3difd.mm"
include "xrsdsreval.mm"
include "abssubd.mm"
include "pm2.61da2ne.mm"
include "3adant1.mm"
include "isxmet2d.mm"
include "trud.mm"

theorem xrsxmet
  let cD: class D
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cJ: class J
  let cP: class P
  let cR: class R
  assume xrsxmet.1: |- D = ( dist ` RR*s )


  assert |- D e. ( *Met ` RR* )

  proof
    cD
    cxr
    cxmt
    cfv
    wcel
    wtru
    vx
    vy
    vz
    cD
    cxr
    cxr
    cvv
    wcel
    wtru
    xrex
    a1i
    cxr
    cxr
    cxp
    cxr
    cD
    wf
    #
    wtru
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    @2
    @1
    cxne
    #
    cxad
    co
    #
    @1
    @2
    cxne
    #
    cxad
    co
    #
    cif
    #
    cxr
    wcel
    #
    vy
    cxr
    wral
    vx
    cxr
    wral
    @0
    @9
    vx
    vy
    cxr
    @1
    cxr
    wcel
    #
    @2
    cxr
    wcel
    #
    wa
    #
    @3
    @5
    @7
    cxr
    @11
    @11
    @4
    cxr
    wcel
    #
    @5
    cxr
    wcel
    #
    @10
    @11
    id
    @1
    xnegcl
    #
    @2
    @4
    xaddcl
    syl2anr
    #
    @11
    @10
    @6
    cxr
    wcel
    #
    @7
    cxr
    wcel
    @2
    xnegcl
    #
    @1
    @6
    xaddcl
    sylan2
    ifcld
    #
    rgen2a
    vx
    vy
    cxr
    cxr
    @8
    cxr
    cD
    vx
    vy
    cD
    xrsxmet.1
    xrsds
    fmpt2
    mpbi
    a1i
    @12
    cc0
    @1
    @2
    cD
    co
    #
    cle
    wbr
    #
    wtru
    @12
    cc0
    @8
    @20
    cle
    @3
    cc0
    @5
    cle
    wbr
    #
    cc0
    @7
    cle
    wbr
    #
    cc0
    @8
    cle
    wbr
    @12
    @5
    @7
    @5
    @8
    cc0
    cle
    breq2
    @7
    @8
    cc0
    cle
    breq2
    @12
    @22
    @3
    @11
    @10
    @22
    @3
    wb
    @2
    @1
    xsubge0
    ancoms
    biimpar
    @12
    @3
    wn
    #
    @2
    @1
    cle
    wbr
    #
    @23
    @12
    @3
    @25
    @1
    @2
    xrletri
    orcanai
    @12
    @23
    @25
    @1
    @2
    xsubge0
    biimpar
    syldan
    ifbothda
    @1
    @2
    cD
    xrsxmet.1
    xrsdsval
    #
    breqtrrd
    #
    adantl
    @12
    @20
    cc0
    cle
    wbr
    #
    vx
    vy
    weq
    #
    wb
    wtru
    @12
    @28
    @28
    @21
    wa
    #
    @20
    cc0
    wceq
    #
    @29
    @12
    @21
    @28
    @27
    biantrud
    @12
    @20
    cxr
    wcel
    cc0
    cxr
    wcel
    #
    @31
    @30
    wb
    @12
    @20
    @8
    cxr
    @26
    @19
    eqeltrd
    0xr
    @20
    cc0
    xrletri3
    sylancl
    @12
    @31
    @29
    @12
    @31
    @29
    @12
    @31
    wa
    #
    @29
    @1
    @2
    @33
    @29
    simpr
    @33
    @1
    @2
    wne
    #
    wa
    #
    @1
    @2
    @35
    @1
    @35
    @1
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    @35
    @20
    cr
    wcel
    #
    @36
    @37
    wa
    #
    @35
    @20
    cc0
    cr
    @12
    @31
    @34
    simplr
    0re
    syl6eqel
    @12
    @34
    @38
    @39
    wb
    #
    @31
    @10
    @11
    @34
    @40
    @1
    @2
    cD
    xrsxmet.1
    xrsdsreclb
    3expa
    adantlr
    mpbid
    #
    simpld
    recnd
    @35
    @2
    @35
    @36
    @37
    @41
    simprd
    recnd
    @35
    @7
    @1
    @2
    cmin
    co
    #
    cc0
    @35
    @39
    @7
    @42
    wceq
    @41
    @1
    @2
    rexsub
    syl
    @35
    @8
    cc0
    wceq
    #
    @7
    cc0
    wceq
    #
    @33
    @43
    @34
    @12
    @31
    @43
    @12
    @20
    @8
    cc0
    @26
    eqeq1d
    biimpa
    adantr
    @35
    @5
    cc0
    wceq
    #
    @44
    wb
    #
    @44
    @44
    wb
    #
    @43
    @44
    wb
    #
    @12
    @46
    @31
    @34
    @12
    @5
    cxne
    #
    cc0
    cxne
    #
    wceq
    #
    @45
    @44
    @12
    @14
    @32
    @51
    @45
    wb
    @16
    0xr
    @5
    cc0
    xneg11
    sylancl
    @12
    @49
    @7
    @50
    cc0
    @12
    @49
    @6
    @4
    cxne
    #
    cxad
    co
    #
    @6
    @1
    cxad
    co
    #
    @7
    @12
    @11
    @13
    @49
    @53
    wceq
    @10
    @11
    simpr
    @10
    @13
    @11
    @15
    adantr
    @2
    @4
    xnegdi
    syl2anc
    @12
    @52
    @1
    @6
    cxad
    @10
    @52
    @1
    wceq
    @11
    @1
    xnegneg
    adantr
    oveq2d
    @12
    @17
    @10
    @54
    @7
    wceq
    @11
    @17
    @10
    @18
    adantl
    @10
    @11
    simpl
    @6
    @1
    xaddcom
    syl2anc
    3eqtrd
    @50
    cc0
    wceq
    @12
    xneg0
    a1i
    eqeq12d
    bitr3d
    ad2antrr
    @35
    @44
    biidd
    @3
    @46
    @47
    @48
    @5
    @7
    @5
    @8
    wceq
    @45
    @43
    @44
    @5
    @8
    cc0
    eqeq1
    bibi1d
    @7
    @8
    wceq
    @44
    @43
    @44
    @7
    @8
    cc0
    eqeq1
    bibi1d
    ifboth
    syl2anc
    mpbid
    eqtr3d
    subeq0d
    pm2.61dane
    ex
    @12
    @31
    @29
    @2
    @2
    cD
    co
    #
    cc0
    wceq
    #
    @11
    @56
    @10
    @11
    @55
    @2
    @2
    cle
    wbr
    #
    @2
    @6
    cxad
    co
    #
    @58
    cif
    #
    @58
    cc0
    @11
    @55
    @59
    wceq
    @2
    @2
    cD
    xrsxmet.1
    xrsdsval
    anidms
    @11
    @57
    @58
    @58
    @2
    xrleid
    iftrued
    @2
    xnegid
    3eqtrd
    #
    adantl
    @29
    @20
    @55
    cc0
    @1
    @2
    @2
    cD
    oveq1
    #
    eqeq1d
    syl5ibrcom
    impbid
    3bitr2d
    adantl
    @10
    @11
    vz
    cv
    #
    cxr
    wcel
    #
    w3a
    #
    @62
    @1
    cD
    co
    #
    cr
    wcel
    #
    @62
    @2
    cD
    co
    #
    cr
    wcel
    #
    wa
    #
    @20
    @65
    @67
    caddc
    co
    #
    cle
    wbr
    #
    wtru
    @64
    @69
    wa
    #
    @71
    @62
    @1
    @62
    @2
    @72
    vz
    vx
    weq
    #
    wa
    #
    @67
    @67
    @20
    @70
    cle
    @74
    @67
    @64
    @66
    @68
    @73
    simplrr
    #
    leidd
    @74
    @62
    @1
    @2
    cD
    @72
    @73
    simpr
    #
    oveq1d
    @74
    @70
    cc0
    @67
    caddc
    co
    @67
    @74
    @65
    cc0
    @67
    caddc
    @74
    @65
    @1
    @1
    cD
    co
    #
    cc0
    @74
    @62
    @1
    @1
    cD
    @76
    oveq1d
    @74
    @10
    @77
    cc0
    wceq
    #
    @10
    @11
    @63
    @69
    @73
    simpll1
    @56
    @78
    vy
    @1
    cxr
    vy
    vx
    weq
    #
    @55
    @77
    cc0
    @79
    @55
    @77
    wceq
    @2
    @1
    @2
    @1
    cD
    oveq12
    anidms
    eqeq1d
    @60
    vtoclga
    syl
    eqtrd
    oveq1d
    @74
    @67
    @74
    @67
    @75
    recnd
    addid2d
    eqtr2d
    3brtr3d
    @72
    vz
    vy
    weq
    #
    wa
    #
    @2
    @1
    cD
    co
    #
    @82
    @20
    @70
    cle
    @81
    @82
    @81
    @65
    @82
    cr
    @81
    @62
    @2
    @1
    cD
    @72
    @80
    simpr
    #
    oveq1d
    #
    @64
    @66
    @68
    @80
    simplrl
    eqeltrrd
    #
    leidd
    @81
    @10
    @11
    @20
    @82
    wceq
    #
    @10
    @11
    @63
    @69
    @80
    simpll1
    @10
    @11
    @63
    @69
    @80
    simpll2
    #
    @12
    @86
    @1
    @2
    @29
    @86
    @12
    @29
    @20
    @55
    @82
    @61
    @1
    @2
    @2
    cD
    oveq2
    eqtr4d
    adantl
    @12
    @34
    wa
    #
    @8
    @25
    @7
    @5
    cif
    #
    @20
    @82
    @25
    @8
    @7
    wceq
    @8
    @5
    wceq
    @8
    @89
    wceq
    @88
    @7
    @5
    @7
    @89
    @8
    eqeq2
    @5
    @89
    @8
    eqeq2
    @88
    @25
    wa
    @3
    @5
    @7
    @88
    @25
    @24
    @88
    @3
    @25
    @88
    @3
    @1
    @2
    clt
    wbr
    #
    @29
    wo
    #
    @90
    @25
    wn
    #
    @12
    @3
    @91
    wb
    @34
    @1
    @2
    xrleloe
    adantr
    @88
    @29
    wn
    #
    @90
    @91
    wb
    @88
    @1
    @2
    @12
    @34
    simpr
    neneqd
    @93
    @90
    @29
    @90
    wo
    @91
    @29
    @90
    biorf
    @29
    @90
    orcom
    syl6bb
    syl
    @12
    @90
    @92
    wb
    @34
    @1
    @2
    xrltnle
    adantr
    3bitr2d
    #
    con2bid
    biimpa
    iffalsed
    @88
    @92
    wa
    @3
    @5
    @7
    @88
    @3
    @92
    @94
    biimpar
    iftrued
    ifbothda
    @12
    @20
    @8
    wceq
    @34
    @26
    adantr
    @12
    @82
    @89
    wceq
    #
    @34
    @11
    @10
    @95
    @2
    @1
    cD
    xrsxmet.1
    xrsdsval
    ancoms
    adantr
    3eqtr4d
    pm2.61dane
    syl2anc
    @81
    @70
    @82
    cc0
    caddc
    co
    @82
    @81
    @65
    @82
    @67
    cc0
    caddc
    @84
    @81
    @67
    @55
    cc0
    @81
    @62
    @2
    @2
    cD
    @83
    oveq1d
    @81
    @11
    @56
    @87
    @60
    syl
    eqtrd
    oveq12d
    @81
    @82
    @81
    @82
    @85
    recnd
    addid1d
    eqtrd
    3brtr4d
    @72
    @62
    @1
    wne
    #
    @62
    @2
    wne
    #
    wa
    #
    wa
    #
    @42
    cabs
    cfv
    #
    @1
    @62
    cmin
    co
    cabs
    cfv
    #
    @62
    @2
    cmin
    co
    cabs
    cfv
    #
    caddc
    co
    @20
    @70
    cle
    @99
    @1
    @2
    @62
    @99
    @1
    @99
    @62
    cr
    wcel
    #
    @36
    @99
    @66
    @103
    @36
    wa
    #
    @64
    @66
    @68
    @98
    simplrl
    @99
    @63
    @10
    @96
    @66
    @104
    wb
    @10
    @11
    @63
    @69
    @98
    simpll3
    #
    @10
    @11
    @63
    @69
    @98
    simpll1
    @72
    @96
    @97
    simprl
    @62
    @1
    cD
    xrsxmet.1
    xrsdsreclb
    syl3anc
    mpbid
    #
    simprd
    #
    recnd
    #
    @99
    @2
    @99
    @103
    @37
    @99
    @68
    @103
    @37
    wa
    #
    @64
    @66
    @68
    @98
    simplrr
    @99
    @63
    @11
    @97
    @68
    @109
    wb
    @105
    @10
    @11
    @63
    @69
    @98
    simpll2
    @72
    @96
    @97
    simprr
    @62
    @2
    cD
    xrsxmet.1
    xrsdsreclb
    syl3anc
    mpbid
    #
    simprd
    #
    recnd
    @99
    @62
    @99
    @103
    @36
    @106
    simpld
    recnd
    #
    abs3difd
    @99
    @36
    @37
    @20
    @100
    wceq
    @107
    @111
    @1
    @2
    cD
    xrsxmet.1
    xrsdsreval
    syl2anc
    @99
    @65
    @101
    @67
    @102
    caddc
    @99
    @65
    @62
    @1
    cmin
    co
    cabs
    cfv
    #
    @101
    @99
    @104
    @65
    @113
    wceq
    @106
    @62
    @1
    cD
    xrsxmet.1
    xrsdsreval
    syl
    @99
    @62
    @1
    @112
    @108
    abssubd
    eqtrd
    @99
    @109
    @67
    @102
    wceq
    @110
    @62
    @2
    cD
    xrsxmet.1
    xrsdsreval
    syl
    oveq12d
    3brtr4d
    pm2.61da2ne
    3adant1
    isxmet2d
    trud
end
