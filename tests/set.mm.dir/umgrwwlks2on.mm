include "cumgr.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cs3.mm"
include "c2.mm"
include "cwwlksnon.mm"
include "co.mm"
include "cv.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "wceq.mm"
include "wex.mm"
include "cpr.mm"
include "cupgr.mm"
include "wb.mm"
include "umgrupgr.mm"
include "adantr.mm"
include "simp1.mm"
include "adantl.mm"
include "simpr3.mm"
include "s3wwlks2on.mm"
include "syl3anc.mm"
include "cc0.mm"
include "cfzo.mm"
include "ciedg.mm"
include "cdm.mm"
include "wf.mm"
include "cfz.mm"
include "c1.mm"
include "eqid.mm"
include "upgr2wlk.mm"
include "syl.mm"
include "s3fv0.mm"
include "3ad2ant1.mm"
include "s3fv1.mm"
include "3ad2ant2.mm"
include "preq12d.mm"
include "eqeq2d.mm"
include "s3fv2.mm"
include "3ad2ant3.mm"
include "anbi12d.mm"
include "3anbi3d.mm"
include "wi.mm"
include "crn.mm"
include "cuhgr.mm"
include "wfun.mm"
include "umgruhgr.mm"
include "uhgrfun.mm"
include "fdmrn.mm"
include "simpr.mm"
include "id.mm"
include "c0ex.mm"
include "prid1.mm"
include "fzo0to2pr.mm"
include "eleqtrri.mm"
include "a1i.mm"
include "ffvelrnd.mm"
include "1ex.mm"
include "prid2.mm"
include "jca.mm"
include "ex.mm"
include "com12.mm"
include "sylbi.mm"
include "3syl.mm"
include "imp.mm"
include "eqcom.mm"
include "biimpi.mm"
include "cedg.mm"
include "edgval.mm"
include "eqtri.mm"
include "eleq12d.mm"
include "mpbird.mm"
include "sylbid.mm"
include "exlimdv.mm"
include "umgr2wlk.mm"
include "c3.mm"
include "caddc.mm"
include "wlklenvp1.mm"
include "oveq1.mm"
include "2p1e3.mm"
include "syl6eq.mm"
include "sylan9eq.mm"
include "3anbi123i.mm"
include "cword.mm"
include "wlkpwrd.mm"
include "ctp.mm"
include "oveq2.mm"
include "fzo0to3tp.mm"
include "tpid1.mm"
include "eleq2.mm"
include "mpbiri.mm"
include "wrdsymbcl.mm"
include "sylan2.mm"
include "tpid2.mm"
include "2ex.mm"
include "tpid3.mm"
include "3jca.mm"
include "3adant3.mm"
include "eleq1.mm"
include "3anbi123d.mm"
include "3exp.mm"
include "impancom.mm"
include "impd.mm"
include "syl2anc.mm"
include "eqwrds3.mm"
include "breq2d.mm"
include "biimpd.mm"
include "pm2.43a.mm"
include "3impib.mm"
include "simpr2.mm"
include "eximdv.mm"
include "syl5com.mm"
include "3expib.mm"
include "com23.mm"
include "impbid.mm"
include "bitrd.mm"

theorem umgrwwlks2on
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let vf: setvar f
  let vp: setvar p
  assume s3wwlks2on.v: |- V = ( Vtx ` G )
  assume usgrwwlks2on.e: |- E = ( Edg ` G )


  assert |- ( ( G e. UMGraph /\ ( A e. V /\ B e. V /\ C e. V ) ) -> ( <" A B C "> e. ( A ( 2 WWalksNOn G ) C ) <-> ( { A , B } e. E /\ { B , C } e. E ) ) )

  proof
    cG
    cumgr
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cB
    cC
    cs3
    #
    cA
    cC
    c2
    cG
    cwwlksnon
    co
    co
    wcel
    #
    vf
    cv
    #
    @6
    cG
    cwlks
    cfv
    #
    wbr
    #
    @8
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    #
    vf
    wex
    #
    cA
    cB
    cpr
    #
    cE
    wcel
    #
    cB
    cC
    cpr
    #
    cE
    wcel
    #
    wa
    #
    @5
    cG
    cupgr
    wcel
    #
    @1
    @3
    @7
    @14
    wb
    @0
    @20
    @4
    cG
    umgrupgr
    #
    adantr
    @4
    @1
    @0
    @1
    @2
    @3
    simp1
    adantl
    @0
    @1
    @2
    @3
    simpr3
    cA
    cB
    cC
    vf
    cG
    cV
    s3wwlks2on.v
    s3wwlks2on
    syl3anc
    @5
    @14
    @19
    @5
    @13
    @19
    vf
    @5
    @13
    cc0
    c2
    cfzo
    co
    #
    cG
    ciedg
    cfv
    #
    cdm
    #
    @8
    wf
    #
    cc0
    c2
    cfz
    co
    cV
    @6
    wf
    #
    cc0
    @8
    cfv
    #
    @23
    cfv
    #
    cc0
    @6
    cfv
    #
    c1
    @6
    cfv
    #
    cpr
    #
    wceq
    #
    c1
    @8
    cfv
    #
    @23
    cfv
    #
    @30
    c2
    @6
    cfv
    #
    cpr
    #
    wceq
    #
    wa
    #
    w3a
    #
    @19
    @0
    @13
    @39
    wb
    #
    @4
    @0
    @20
    @40
    @21
    @6
    @8
    cG
    @23
    cV
    s3wwlks2on.v
    @23
    eqid
    #
    upgr2wlk
    syl
    adantr
    @5
    @39
    @25
    @26
    @28
    @15
    wceq
    #
    @34
    @17
    wceq
    #
    wa
    #
    w3a
    #
    @19
    @5
    @38
    @44
    @25
    @26
    @4
    @38
    @44
    wb
    @0
    @4
    @32
    @42
    @37
    @43
    @4
    @31
    @15
    @28
    @4
    @29
    cA
    @30
    cB
    @1
    @2
    @29
    cA
    wceq
    @3
    cA
    cB
    cC
    cV
    s3fv0
    3ad2ant1
    @2
    @1
    @30
    cB
    wceq
    @3
    cA
    cB
    cC
    cV
    s3fv1
    3ad2ant2
    #
    preq12d
    eqeq2d
    @4
    @36
    @17
    @34
    @4
    @30
    cB
    @35
    cC
    @46
    @3
    @1
    @35
    cC
    wceq
    @2
    cA
    cB
    cC
    cV
    s3fv2
    3ad2ant3
    preq12d
    eqeq2d
    anbi12d
    adantl
    3anbi3d
    @0
    @45
    @19
    wi
    @4
    @0
    @45
    @19
    @0
    @45
    wa
    #
    @19
    @28
    @23
    crn
    #
    wcel
    #
    @34
    @48
    wcel
    #
    wa
    #
    @0
    @45
    @51
    @0
    cG
    cuhgr
    wcel
    @23
    wfun
    #
    @45
    @51
    wi
    #
    cG
    umgruhgr
    @23
    cG
    @41
    uhgrfun
    @52
    @24
    @48
    @23
    wf
    #
    @53
    @23
    fdmrn
    @45
    @54
    @51
    @25
    @26
    @54
    @51
    wi
    @44
    @25
    @54
    @51
    @25
    @54
    wa
    #
    @49
    @50
    @55
    @24
    @48
    @27
    @23
    @25
    @54
    simpr
    #
    @25
    @27
    @24
    wcel
    @54
    @25
    @22
    @24
    cc0
    @8
    @25
    id
    #
    cc0
    @22
    wcel
    @25
    cc0
    cc0
    c1
    cpr
    #
    @22
    cc0
    c1
    c0ex
    prid1
    fzo0to2pr
    eleqtrri
    a1i
    ffvelrnd
    adantr
    ffvelrnd
    @55
    @24
    @48
    @33
    @23
    @56
    @25
    @33
    @24
    wcel
    @54
    @25
    @22
    @24
    c1
    @8
    @57
    c1
    @22
    wcel
    @25
    c1
    @58
    @22
    cc0
    c1
    1ex
    prid2
    fzo0to2pr
    eleqtrri
    a1i
    ffvelrnd
    adantr
    ffvelrnd
    jca
    ex
    3ad2ant1
    com12
    sylbi
    3syl
    imp
    @47
    @16
    @49
    @18
    @50
    @47
    @15
    @28
    cE
    @48
    @45
    @15
    @28
    wceq
    #
    @0
    @44
    @25
    @59
    @26
    @42
    @59
    @43
    @42
    @59
    @28
    @15
    eqcom
    biimpi
    adantr
    3ad2ant3
    adantl
    cE
    @48
    wceq
    @47
    cE
    cG
    cedg
    cfv
    @48
    usgrwwlks2on.e
    cG
    edgval
    eqtri
    a1i
    #
    eleq12d
    @47
    @17
    @34
    cE
    @48
    @45
    @17
    @34
    wceq
    #
    @0
    @44
    @25
    @61
    @26
    @43
    @61
    @42
    @43
    @61
    @34
    @17
    eqcom
    biimpi
    adantl
    3ad2ant3
    adantl
    @60
    eleq12d
    anbi12d
    mpbird
    ex
    adantr
    sylbid
    sylbid
    exlimdv
    @0
    @4
    @19
    @14
    wi
    @0
    @19
    @4
    @14
    @0
    @16
    @18
    @4
    @14
    wi
    @0
    @16
    @18
    w3a
    @8
    vp
    cv
    #
    @9
    wbr
    #
    @12
    cA
    cc0
    @62
    cfv
    #
    wceq
    #
    cB
    c1
    @62
    cfv
    #
    wceq
    #
    cC
    c2
    @62
    cfv
    #
    wceq
    #
    w3a
    #
    w3a
    #
    vp
    wex
    #
    vf
    wex
    @4
    @14
    cA
    cB
    cC
    vf
    cE
    cG
    vp
    usgrwwlks2on.e
    umgr2wlk
    @4
    @72
    @13
    vf
    @4
    @71
    @13
    vp
    @4
    @71
    @13
    @4
    @71
    wa
    @10
    @12
    @71
    @10
    @4
    @63
    @12
    @70
    @10
    @12
    @70
    wa
    #
    @63
    @10
    @63
    @73
    @63
    @10
    wi
    @63
    @73
    wa
    #
    @63
    @10
    @74
    @62
    @6
    @8
    @9
    @74
    @62
    @6
    wceq
    #
    @62
    chash
    cfv
    #
    c3
    wceq
    #
    @64
    cA
    wceq
    #
    @66
    cB
    wceq
    #
    @68
    cC
    wceq
    #
    w3a
    #
    wa
    #
    @74
    @77
    @81
    @63
    @73
    @76
    @11
    c1
    caddc
    co
    #
    c3
    @62
    @8
    cG
    wlklenvp1
    #
    @12
    @83
    c3
    wceq
    @70
    @12
    @83
    c2
    c1
    caddc
    co
    c3
    @11
    c2
    c1
    caddc
    oveq1
    2p1e3
    syl6eq
    #
    adantr
    sylan9eq
    @73
    @81
    @63
    @70
    @81
    @12
    @70
    @81
    @65
    @78
    @67
    @79
    @69
    @80
    cA
    @64
    eqcom
    cB
    @66
    eqcom
    cC
    @68
    eqcom
    3anbi123i
    biimpi
    adantl
    adantl
    jca
    @74
    @62
    cV
    cword
    wcel
    #
    @4
    wa
    #
    @75
    @82
    wb
    @63
    @73
    @87
    @63
    @86
    @76
    @83
    wceq
    #
    @73
    @87
    wi
    @62
    @8
    cG
    cV
    s3wwlks2on.v
    wlkpwrd
    @84
    @86
    @88
    wa
    @12
    @70
    @87
    @86
    @12
    @88
    @70
    @87
    wi
    #
    @86
    @12
    wa
    @88
    @77
    @89
    @12
    @88
    @77
    wb
    @86
    @12
    @83
    c3
    @76
    @85
    eqeq2d
    adantl
    @86
    @77
    @89
    wi
    @12
    @86
    @77
    @70
    @87
    @86
    @77
    @70
    w3a
    #
    @86
    @4
    @86
    @77
    @70
    simp1
    @90
    @4
    @64
    cV
    wcel
    #
    @66
    cV
    wcel
    #
    @68
    cV
    wcel
    #
    w3a
    #
    @86
    @77
    @94
    @70
    @77
    @86
    cc0
    @76
    cfzo
    co
    #
    cc0
    c1
    c2
    ctp
    #
    wceq
    #
    @94
    @77
    @95
    cc0
    c3
    cfzo
    co
    @96
    @76
    c3
    cc0
    cfzo
    oveq2
    fzo0to3tp
    syl6eq
    @86
    @97
    wa
    @91
    @92
    @93
    @97
    @86
    cc0
    @95
    wcel
    #
    @91
    @97
    @98
    cc0
    @96
    wcel
    cc0
    c1
    c2
    c0ex
    tpid1
    @95
    @96
    cc0
    eleq2
    mpbiri
    cc0
    cV
    @62
    wrdsymbcl
    sylan2
    @97
    @86
    c1
    @95
    wcel
    #
    @92
    @97
    @99
    c1
    @96
    wcel
    cc0
    c1
    c2
    1ex
    tpid2
    @95
    @96
    c1
    eleq2
    mpbiri
    c1
    cV
    @62
    wrdsymbcl
    sylan2
    @97
    @86
    c2
    @95
    wcel
    #
    @93
    @97
    @100
    c2
    @96
    wcel
    cc0
    c1
    c2
    2ex
    tpid3
    @95
    @96
    c2
    eleq2
    mpbiri
    c2
    cV
    @62
    wrdsymbcl
    sylan2
    3jca
    sylan2
    3adant3
    @70
    @86
    @4
    @94
    wb
    @77
    @70
    @1
    @91
    @2
    @92
    @3
    @93
    @65
    @67
    @1
    @91
    wb
    @69
    cA
    @64
    cV
    eleq1
    3ad2ant1
    @67
    @65
    @2
    @92
    wb
    @69
    cB
    @66
    cV
    eleq1
    3ad2ant2
    @69
    @65
    @3
    @93
    wb
    @67
    cC
    @68
    cV
    eleq1
    3ad2ant3
    3anbi123d
    3ad2ant3
    mpbird
    jca
    3exp
    adantr
    sylbid
    impancom
    impd
    syl2anc
    imp
    cA
    cB
    cC
    cV
    @62
    eqwrds3
    syl
    mpbird
    breq2d
    biimpd
    ex
    pm2.43a
    3impib
    adantl
    @4
    @63
    @12
    @70
    simpr2
    jca
    ex
    exlimdv
    eximdv
    syl5com
    3expib
    com23
    imp
    impbid
    bitrd
end
