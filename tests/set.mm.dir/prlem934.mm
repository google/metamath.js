include "cnp.mm"
include "wcel.mm"
include "cv.mm"
include "cplq.mm"
include "co.mm"
include "wral.mm"
include "wn.mm"
include "wrex.mm"
include "cnq.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "prn0.mm"
include "r19.2z.mm"
include "ex.mm"
include "syl.mm"
include "prpssnq.mm"
include "pssssd.mm"
include "sseld.mm"
include "cxp.mm"
include "addnqf.mm"
include "fdmi.mm"
include "0nnq.mm"
include "ndmovrcl.mm"
include "simprd.mm"
include "syl6com.mm"
include "rexlimivw.mm"
include "com12.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "notbid.mm"
include "imbi2d.mm"
include "wa.mm"
include "wss.mm"
include "wpss.mm"
include "dfpss2.mm"
include "sylib.mm"
include "adantr.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "wex.mm"
include "simpl1.mm"
include "n0.mm"
include "crq.mm"
include "cfv.mm"
include "cmq.mm"
include "c1o.mm"
include "cop.mm"
include "cltq.mm"
include "wbr.mm"
include "cnpi.mm"
include "simprl.mm"
include "simpl2.mm"
include "recclnq.mm"
include "mulclnq.mm"
include "archnq.mm"
include "sylan2.mm"
include "syl2anc.mm"
include "simpll2.mm"
include "simplrl.mm"
include "simprr.mm"
include "wb.mm"
include "ltmnq.mm"
include "vex.mm"
include "fvex.mm"
include "mulcomnq.mm"
include "mulassnq.mm"
include "caov12.mm"
include "breq12i.mm"
include "syl6bb.mm"
include "c1q.mm"
include "recidnq.mm"
include "oveq2d.mm"
include "mulidnq.mm"
include "sylan9eq.mm"
include "breq1d.mm"
include "bitrd.mm"
include "biimpa.mm"
include "syl21anc.mm"
include "pinq.mm"
include "sylan.mm"
include "simpll1.mm"
include "simplrr.mm"
include "elprnq.mm"
include "ltaddnq.mm"
include "addcomnq.mm"
include "syl6breq.mm"
include "ltsonq.mm"
include "ltrelnq.mm"
include "sotri.mm"
include "simpll3.mm"
include "cpli.mm"
include "opeq1.mm"
include "df-1nq.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "syl5eq.mm"
include "oveq1.mm"
include "rspccva.mm"
include "biimpar.mm"
include "syl2an.mm"
include "3impb.mm"
include "3simpa.mm"
include "addassnq.mm"
include "opex.mm"
include "1nq.mm"
include "elexi.mm"
include "distrnq.mm"
include "caovdir.mm"
include "a1i.mm"
include "cplpq.mm"
include "cerq.mm"
include "addpqnq.mm"
include "sylancl.mm"
include "cmi.mm"
include "oveq2i.mm"
include "1pi.mm"
include "addpipq.mm"
include "mpanr12.mm"
include "mpan2.mm"
include "mulidpi.mm"
include "mp1i.mm"
include "oveq12d.mm"
include "opeq12d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "addclpi.mm"
include "nqerid.mm"
include "3syl.mm"
include "3eqtrd.mm"
include "adantl.mm"
include "3eqtr3rd.mm"
include "syl5ib.mm"
include "expd.mm"
include "expimpd.mm"
include "syl5.mm"
include "a2d.mm"
include "indpi.mm"
include "imp.mm"
include "syl13anc.mm"
include "prcdnq.mm"
include "mpd.mm"
include "rexlimddv.mm"
include "expr.mm"
include "exlimdv.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "3expia.mm"
include "mtod.mm"
include "expcom.mm"
include "vtoclga.mm"
include "3syld.mm"
include "pm2.01d.mm"
include "rexnal.mm"
include "sylibr.mm"

theorem prlem934
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vb: setvar b
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  assume prlem934.1: |- B e. _V

  disjoint A x
  disjoint B x
  disjoint A b
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B b
  disjoint b v
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  assert |- ( A e. P. -> E. x e. A -. ( x +Q B ) e. A )

  proof
    cA
    cnp
    wcel
    #
    vx
    cv
    #
    cB
    cplq
    co
    #
    cA
    wcel
    #
    vx
    cA
    wral
    #
    wn
    #
    @3
    wn
    vx
    cA
    wrex
    @0
    @4
    @0
    @4
    @3
    vx
    cA
    wrex
    #
    cB
    cnq
    wcel
    #
    @5
    @0
    cA
    c0
    wne
    #
    @4
    @6
    wi
    cA
    prn0
    #
    @8
    @4
    @6
    @3
    vx
    cA
    r19.2z
    ex
    syl
    @6
    @0
    @7
    @3
    @0
    @7
    wi
    vx
    cA
    @0
    @3
    @2
    cnq
    wcel
    #
    @7
    @0
    cA
    cnq
    @2
    @0
    cA
    cnq
    cA
    prpssnq
    #
    pssssd
    #
    sseld
    @10
    @1
    cnq
    wcel
    @7
    @1
    cB
    cnq
    cplq
    cnq
    cnq
    cxp
    cnq
    cplq
    addnqf
    fdmi
    0nnq
    ndmovrcl
    simprd
    syl6com
    rexlimivw
    com12
    @7
    @0
    @5
    @0
    @1
    vb
    cv
    #
    cplq
    co
    #
    cA
    wcel
    #
    vx
    cA
    wral
    #
    wn
    #
    wi
    @0
    @5
    wi
    vb
    cB
    cnq
    @13
    cB
    wceq
    #
    @17
    @5
    @0
    @18
    @16
    @4
    @18
    @15
    @3
    vx
    cA
    @18
    @14
    @2
    cA
    @13
    cB
    @1
    cplq
    oveq2
    eleq1d
    ralbidv
    notbid
    imbi2d
    @0
    @13
    cnq
    wcel
    #
    @17
    @0
    @19
    wa
    @16
    cA
    cnq
    wceq
    #
    @0
    @20
    wn
    #
    @19
    @0
    cA
    cnq
    wss
    #
    @21
    @0
    cA
    cnq
    wpss
    @22
    @21
    wa
    @11
    cA
    cnq
    dfpss2
    sylib
    simprd
    adantr
    @0
    @19
    @16
    @20
    @0
    @19
    @16
    w3a
    #
    cA
    cnq
    @0
    @19
    @22
    @16
    @12
    3ad2ant1
    @23
    vw
    cnq
    cA
    @23
    vw
    cv
    #
    cnq
    wcel
    #
    @24
    cA
    wcel
    #
    @23
    @25
    wa
    #
    vy
    cv
    #
    cA
    wcel
    #
    vy
    wex
    #
    @26
    @27
    @0
    @30
    @0
    @19
    @16
    @25
    simpl1
    @0
    @8
    @30
    @9
    vy
    cA
    n0
    sylib
    syl
    @27
    @29
    @26
    vy
    @23
    @25
    @29
    @26
    @23
    @25
    @29
    wa
    #
    wa
    #
    @24
    @13
    crq
    cfv
    #
    cmq
    co
    #
    vz
    cv
    #
    c1o
    cop
    #
    cltq
    wbr
    #
    @26
    vz
    cnpi
    @32
    @25
    @19
    @37
    vz
    cnpi
    wrex
    #
    @23
    @25
    @29
    simprl
    @0
    @19
    @16
    @31
    simpl2
    @19
    @25
    @33
    cnq
    wcel
    #
    @38
    @13
    recclnq
    @25
    @39
    wa
    @34
    cnq
    wcel
    @38
    @24
    @33
    mulclnq
    vz
    @34
    archnq
    syl
    sylan2
    syl2anc
    @32
    @35
    cnpi
    wcel
    #
    @37
    wa
    #
    wa
    #
    @24
    @28
    @36
    @13
    cmq
    co
    #
    cplq
    co
    #
    cltq
    wbr
    #
    @26
    @42
    @24
    @43
    cltq
    wbr
    #
    @43
    @44
    cltq
    wbr
    #
    @45
    @42
    @19
    @25
    @37
    @46
    @0
    @19
    @16
    @31
    @41
    simpll2
    #
    @23
    @25
    @29
    @41
    simplrl
    @32
    @40
    @37
    simprr
    @19
    @25
    wa
    #
    @37
    @46
    @49
    @37
    @24
    @13
    @33
    cmq
    co
    #
    cmq
    co
    #
    @43
    cltq
    wbr
    #
    @46
    @19
    @37
    @52
    wb
    @25
    @19
    @37
    @13
    @34
    cmq
    co
    #
    @13
    @36
    cmq
    co
    #
    cltq
    wbr
    @52
    @34
    @36
    @13
    ltmnq
    @53
    @51
    @54
    @43
    cltq
    vv
    vx
    vy
    @13
    @24
    @33
    cmq
    vb
    vex
    #
    vw
    vex
    @13
    crq
    fvex
    vv
    cv
    #
    @1
    mulcomnq
    #
    @56
    @1
    @28
    mulassnq
    caov12
    @13
    @36
    mulcomnq
    breq12i
    syl6bb
    adantr
    @49
    @51
    @24
    @43
    cltq
    @19
    @25
    @51
    @24
    c1q
    cmq
    co
    @24
    @19
    @50
    c1q
    @24
    cmq
    @13
    recidnq
    oveq2d
    @24
    mulidnq
    sylan9eq
    breq1d
    bitrd
    biimpa
    syl21anc
    @42
    @43
    cnq
    wcel
    #
    @28
    cnq
    wcel
    #
    @47
    @42
    @40
    @19
    @58
    @32
    @40
    @37
    simprl
    #
    @48
    @40
    @36
    cnq
    wcel
    #
    @19
    @58
    @35
    pinq
    #
    @36
    @13
    mulclnq
    sylan
    syl2anc
    @42
    @0
    @29
    @59
    @0
    @19
    @16
    @31
    @41
    simpll1
    #
    @23
    @25
    @29
    @41
    simplrr
    #
    cA
    @28
    elprnq
    syl2anc
    @58
    @59
    wa
    @43
    @43
    @28
    cplq
    co
    @44
    cltq
    @43
    @28
    ltaddnq
    @43
    @28
    addcomnq
    syl6breq
    syl2anc
    @24
    @43
    @44
    cltq
    cnq
    ltsonq
    ltrelnq
    sotri
    syl2anc
    @42
    @0
    @44
    cA
    wcel
    #
    @45
    @26
    wi
    @63
    @42
    @40
    @19
    @16
    @29
    @65
    @60
    @48
    @0
    @19
    @16
    @31
    @41
    simpll3
    @64
    @40
    @19
    @16
    @29
    w3a
    #
    @65
    @66
    @28
    @24
    c1o
    cop
    #
    @13
    cmq
    co
    #
    cplq
    co
    #
    cA
    wcel
    #
    wi
    @66
    @28
    c1q
    @13
    cmq
    co
    #
    cplq
    co
    #
    cA
    wcel
    #
    wi
    @66
    @65
    wi
    #
    @66
    @28
    @35
    c1o
    cpli
    co
    #
    c1o
    cop
    #
    @13
    cmq
    co
    #
    cplq
    co
    #
    cA
    wcel
    #
    wi
    @74
    vw
    vz
    @35
    @24
    c1o
    wceq
    #
    @70
    @73
    @66
    @80
    @69
    @72
    cA
    @80
    @68
    @71
    @28
    cplq
    @80
    @67
    c1q
    @13
    cmq
    @80
    @67
    c1o
    c1o
    cop
    #
    c1q
    @24
    c1o
    c1o
    opeq1
    df-1nq
    syl6eqr
    oveq1d
    oveq2d
    eleq1d
    imbi2d
    @24
    @35
    wceq
    #
    @70
    @65
    @66
    @82
    @69
    @44
    cA
    @82
    @68
    @43
    @28
    cplq
    @82
    @67
    @36
    @13
    cmq
    @24
    @35
    c1o
    opeq1
    oveq1d
    oveq2d
    eleq1d
    imbi2d
    #
    @24
    @75
    wceq
    #
    @70
    @79
    @66
    @84
    @69
    @78
    cA
    @84
    @68
    @77
    @28
    cplq
    @84
    @67
    @76
    @13
    cmq
    @24
    @75
    c1o
    opeq1
    oveq1d
    oveq2d
    eleq1d
    imbi2d
    @83
    @19
    @16
    @29
    @73
    @19
    @71
    @13
    wceq
    #
    @28
    @13
    cplq
    co
    #
    cA
    wcel
    #
    @73
    @16
    @29
    wa
    @19
    @71
    @13
    c1q
    cmq
    co
    @13
    c1q
    @13
    mulcomnq
    @13
    mulidnq
    syl5eq
    #
    @15
    @87
    vx
    @28
    cA
    @1
    @28
    wceq
    @14
    @86
    cA
    @1
    @28
    @13
    cplq
    oveq1
    eleq1d
    rspccva
    @85
    @73
    @87
    @85
    @72
    @86
    cA
    @71
    @13
    @28
    cplq
    oveq2
    eleq1d
    biimpar
    syl2an
    3impb
    @40
    @66
    @65
    @79
    @66
    @19
    @16
    wa
    @40
    @65
    @79
    wi
    #
    @19
    @16
    @29
    3simpa
    @40
    @19
    @16
    @89
    @40
    @19
    wa
    #
    @16
    @65
    @79
    @16
    @65
    wa
    @44
    @13
    cplq
    co
    #
    cA
    wcel
    #
    @90
    @79
    @15
    @92
    vx
    @44
    cA
    @1
    @44
    wceq
    @14
    @91
    cA
    @1
    @44
    @13
    cplq
    oveq1
    eleq1d
    rspccva
    @90
    @91
    @78
    cA
    @90
    @91
    @28
    @43
    @13
    cplq
    co
    #
    cplq
    co
    @78
    @28
    @43
    @13
    addassnq
    @90
    @93
    @77
    @28
    cplq
    @90
    @36
    c1q
    cplq
    co
    #
    @13
    cmq
    co
    #
    @43
    @71
    cplq
    co
    #
    @77
    @93
    @95
    @96
    wceq
    @90
    vv
    vx
    vy
    @36
    c1q
    @13
    cplq
    cmq
    @35
    c1o
    opex
    c1q
    cnq
    1nq
    elexi
    @55
    @57
    @56
    @1
    @28
    distrnq
    caovdir
    a1i
    @90
    @94
    @76
    @13
    cmq
    @40
    @94
    @76
    wceq
    @19
    @40
    @94
    @36
    c1q
    cplpq
    co
    #
    cerq
    cfv
    #
    @76
    cerq
    cfv
    #
    @76
    @40
    @61
    c1q
    cnq
    wcel
    @94
    @98
    wceq
    @62
    1nq
    @36
    c1q
    addpqnq
    sylancl
    @40
    @97
    @76
    cerq
    @40
    @97
    @35
    c1o
    cmi
    co
    #
    c1o
    c1o
    cmi
    co
    #
    cpli
    co
    #
    @101
    cop
    #
    @76
    @40
    @97
    @36
    @81
    cplpq
    co
    #
    @103
    c1q
    @81
    @36
    cplpq
    df-1nq
    oveq2i
    @40
    c1o
    cnpi
    wcel
    #
    @104
    @103
    wceq
    #
    1pi
    @40
    @105
    wa
    @105
    @105
    @106
    1pi
    1pi
    @35
    c1o
    c1o
    c1o
    addpipq
    mpanr12
    mpan2
    syl5eq
    @40
    @102
    @75
    @101
    c1o
    @40
    @100
    @35
    @101
    c1o
    cpli
    @35
    mulidpi
    @105
    @101
    c1o
    wceq
    @40
    1pi
    c1o
    mulidpi
    mp1i
    #
    oveq12d
    @107
    opeq12d
    eqtrd
    fveq2d
    @40
    @75
    cnpi
    wcel
    #
    @76
    cnq
    wcel
    @99
    @76
    wceq
    @40
    @105
    @108
    1pi
    @35
    c1o
    addclpi
    mpan2
    @75
    pinq
    @76
    nqerid
    3syl
    3eqtrd
    adantr
    oveq1d
    @90
    @71
    @13
    @43
    cplq
    @19
    @85
    @40
    @88
    adantl
    oveq2d
    3eqtr3rd
    oveq2d
    syl5eq
    eleq1d
    syl5ib
    expd
    expimpd
    syl5
    a2d
    indpi
    imp
    syl13anc
    cA
    @44
    @24
    prcdnq
    syl2anc
    mpd
    rexlimddv
    expr
    exlimdv
    mpd
    ex
    ssrdv
    eqssd
    3expia
    mtod
    expcom
    vtoclga
    com12
    3syld
    pm2.01d
    @3
    vx
    cA
    rexnal
    sylibr
end
