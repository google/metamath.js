include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cmin.mm"
include "wceq.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wo.mm"
include "wi.mm"
include "cn.mm"
include "wral.mm"
include "clt.mm"
include "cdiv.mm"
include "1red.mm"
include "perfectlem1.mm"
include "simp3d.mm"
include "nnred.mm"
include "nnge1d.mm"
include "cc.mm"
include "2cn.mm"
include "exp1.mm"
include "ax-mp.mm"
include "df-2.mm"
include "eqtri.mm"
include "cr.mm"
include "cz.mm"
include "2re.mm"
include "a1i.mm"
include "1zzd.mm"
include "peano2nnd.mm"
include "nnzd.mm"
include "1lt2.mm"
include "crp.mm"
include "1re.mm"
include "nnrpd.mm"
include "ltaddrp.mm"
include "sylancr.mm"
include "ax-1cn.mm"
include "nncnd.mm"
include "addcom.mm"
include "breqtrd.mm"
include "ltexp2a.mm"
include "syl32anc.mm"
include "syl5eqbrr.mm"
include "simp1d.mm"
include "ltaddsubd.mm"
include "mpbid.mm"
include "cc0.mm"
include "wb.mm"
include "0lt1.mm"
include "peano2rem.mm"
include "syl.mm"
include "expgt1.mm"
include "syl3anc.mm"
include "posdif.mm"
include "nngt0d.mm"
include "ltdiv2.mm"
include "syl222anc.mm"
include "div1d.mm"
include "lelttrd.mm"
include "eluz2b2.mm"
include "sylanbrc.mm"
include "wa.mm"
include "cpr.mm"
include "cmul.mm"
include "cle.mm"
include "wn.mm"
include "ctp.mm"
include "csu.mm"
include "crab.mm"
include "cfn.mm"
include "cfz.mm"
include "wss.mm"
include "fzfid.mm"
include "dvdsssfz1.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "ad2antrr.mm"
include "ssrab2.mm"
include "sselda.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "csn.mm"
include "cun.mm"
include "df-tp.mm"
include "prssi.mm"
include "simplrl.mm"
include "snssd.mm"
include "unssd.mm"
include "syl5eqss.mm"
include "weq.mm"
include "w3o.mm"
include "eltpi.mm"
include "simp2d.mm"
include "dvdsmul2.mm"
include "nnne0d.mm"
include "divcan2d.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "iddvds.mm"
include "simplrr.mm"
include "3jaod.mm"
include "syl5.mm"
include "imp.mm"
include "ssrabdv.mm"
include "fsumless.mm"
include "cin.mm"
include "c0.mm"
include "simpr.mm"
include "disjsn.mm"
include "sylibr.mm"
include "tpfi.mm"
include "fsumsplit.mm"
include "id.mm"
include "sumsn.mm"
include "oveq12d.mm"
include "incom.mm"
include "wne.mm"
include "gtned.mm"
include "disjsn2.mm"
include "syl5eqr.mm"
include "df-pr.mm"
include "prfi.mm"
include "mulcld.mm"
include "divdird.mm"
include "1cnd.mm"
include "subdird.mm"
include "mulid2d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "pncan3d.mm"
include "oveq1d.mm"
include "divassd.mm"
include "divcan3d.mm"
include "3eqtr3d.mm"
include "3eqtr4d.mm"
include "csgm.mm"
include "ccxp.mm"
include "cn0.mm"
include "expp1.mm"
include "2nn.mm"
include "nnexpcl.mm"
include "mulcom.mm"
include "sylancl.mm"
include "2cnd.mm"
include "mulassd.mm"
include "cgcd.mm"
include "2prm.mm"
include "coprm.mm"
include "2z.mm"
include "rpexp1i.mm"
include "mpd.mm"
include "sgmmul.mm"
include "syl13anc.mm"
include "pncan.mm"
include "1sgm2ppw.mm"
include "eqtr3d.mm"
include "3eqtrd.mm"
include "1nn0.mm"
include "sgmnncl.mm"
include "sgmval.mm"
include "sseldi.mm"
include "cxp1d.mm"
include "sumeq2dv.mm"
include "3eqtrrd.mm"
include "3brtr3d.mm"
include "remulcld.mm"
include "ltaddrpd.mm"
include "readdcld.mm"
include "ltnled.mm"
include "condan.mm"
include "elpri.mm"
include "expr.mm"
include "ralrimiva.mm"
include "necomd.mm"
include "1nn.mm"
include "1dvds.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "ord.mm"
include "necon1ad.mm"
include "eqeq2d.mm"
include "orbi1d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "mpbird.mm"
include "isprm2.mm"
include "ltp1d.mm"
include "peano2re.mm"
include "snssi.mm"
include "mp1i.mm"
include "adantr.mm"
include "diveq1ad.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "nelprd.mm"
include "ex.mm"
include "necon1bd.mm"
include "jca.mm"

theorem perfectlem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  assume perfectlem.1: |- ( ph -> A e. NN )
  assume perfectlem.2: |- ( ph -> B e. NN )
  assume perfectlem.3: |- ( ph -> -. 2 || B )
  assume perfectlem.4: |- ( ph -> ( 1 sigma ( ( 2 ^ A ) x. B ) ) = ( 2 x. ( ( 2 ^ A ) x. B ) ) )


  assert |- ( ph -> ( B e. Prime /\ B = ( ( 2 ^ ( A + 1 ) ) - 1 ) ) )

  proof
    wph
    cB
    cprime
    wcel
    #
    cB
    c2
    cA
    c1
    caddc
    co
    #
    cexp
    co
    #
    c1
    cmin
    co
    #
    wceq
    #
    wph
    cB
    c2
    cuz
    cfv
    wcel
    #
    vn
    cv
    #
    cB
    cdvds
    wbr
    #
    @6
    c1
    wceq
    #
    @6
    cB
    wceq
    #
    wo
    #
    wi
    #
    vn
    cn
    wral
    #
    @0
    wph
    cB
    cn
    wcel
    #
    c1
    cB
    clt
    wbr
    @5
    perfectlem.2
    wph
    c1
    cB
    @3
    cdiv
    co
    #
    cB
    wph
    1red
    #
    wph
    @14
    wph
    @2
    cn
    wcel
    #
    @3
    cn
    wcel
    #
    @14
    cn
    wcel
    #
    wph
    cA
    cB
    perfectlem.1
    perfectlem.2
    perfectlem.3
    perfectlem.4
    perfectlem1
    #
    simp3d
    #
    nnred
    #
    wph
    cB
    perfectlem.2
    nnred
    #
    wph
    @14
    @20
    nnge1d
    wph
    @14
    cB
    c1
    cdiv
    co
    #
    cB
    clt
    wph
    c1
    @3
    clt
    wbr
    #
    @14
    @23
    clt
    wbr
    #
    wph
    c1
    c1
    caddc
    co
    #
    @2
    clt
    wbr
    @24
    wph
    @26
    c2
    c1
    cexp
    co
    #
    @2
    clt
    @27
    c2
    @26
    c2
    cc
    wcel
    #
    @27
    c2
    wceq
    2cn
    c2
    exp1
    ax-mp
    df-2
    eqtri
    wph
    c2
    cr
    wcel
    #
    c1
    cz
    wcel
    @1
    cz
    wcel
    c1
    c2
    clt
    wbr
    #
    c1
    @1
    clt
    wbr
    @27
    @2
    clt
    wbr
    @29
    wph
    2re
    a1i
    #
    wph
    1zzd
    wph
    @1
    wph
    cA
    perfectlem.1
    peano2nnd
    #
    nnzd
    @30
    wph
    1lt2
    a1i
    #
    wph
    c1
    c1
    cA
    caddc
    co
    #
    @1
    clt
    wph
    c1
    cr
    wcel
    #
    cA
    crp
    wcel
    c1
    @34
    clt
    wbr
    1re
    wph
    cA
    perfectlem.1
    nnrpd
    c1
    cA
    ltaddrp
    sylancr
    wph
    c1
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    @34
    @1
    wceq
    ax-1cn
    wph
    cA
    perfectlem.1
    nncnd
    #
    c1
    cA
    addcom
    sylancr
    breqtrd
    c2
    c1
    @1
    ltexp2a
    syl32anc
    syl5eqbrr
    wph
    c1
    c1
    @2
    @15
    @15
    wph
    @2
    wph
    @16
    @17
    @18
    @19
    simp1d
    #
    nnred
    #
    ltaddsubd
    mpbid
    wph
    @35
    cc0
    c1
    clt
    wbr
    #
    @3
    cr
    wcel
    #
    cc0
    @3
    clt
    wbr
    #
    cB
    cr
    wcel
    cc0
    cB
    clt
    wbr
    @24
    @25
    wb
    @15
    @41
    wph
    0lt1
    a1i
    wph
    @2
    cr
    wcel
    #
    @42
    @40
    @2
    peano2rem
    syl
    wph
    c1
    @2
    clt
    wbr
    #
    @43
    wph
    @29
    @1
    cn
    wcel
    #
    @30
    @45
    @31
    @32
    @33
    c2
    @1
    expgt1
    syl3anc
    wph
    @35
    @44
    @45
    @43
    wb
    1re
    @40
    c1
    @2
    posdif
    sylancr
    mpbid
    @22
    wph
    cB
    perfectlem.2
    nngt0d
    c1
    @3
    cB
    ltdiv2
    syl222anc
    mpbid
    wph
    cB
    wph
    cB
    perfectlem.2
    nncnd
    #
    div1d
    breqtrd
    #
    lelttrd
    #
    cB
    eluz2b2
    sylanbrc
    wph
    @12
    @7
    @6
    @14
    wceq
    #
    @9
    wo
    #
    wi
    #
    vn
    cn
    wral
    #
    wph
    @52
    vn
    cn
    wph
    @6
    cn
    wcel
    #
    @7
    @51
    wph
    @54
    @7
    wa
    #
    wa
    #
    @6
    @14
    cB
    cpr
    #
    wcel
    #
    @51
    @56
    @58
    @2
    @14
    cmul
    co
    #
    @6
    caddc
    co
    #
    @59
    cle
    wbr
    #
    @56
    @58
    wn
    #
    wa
    #
    @14
    cB
    @6
    ctp
    #
    vk
    cv
    #
    vk
    csu
    #
    vx
    cv
    #
    cB
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    @65
    vk
    csu
    #
    @60
    @59
    cle
    @63
    @69
    @65
    @64
    vk
    wph
    @69
    cfn
    wcel
    #
    @55
    @62
    wph
    c1
    cB
    cfz
    co
    #
    cfn
    wcel
    @69
    @72
    wss
    #
    @71
    wph
    c1
    cB
    fzfid
    wph
    @13
    @73
    perfectlem.2
    cB
    vx
    dvdsssfz1
    syl
    @72
    @69
    ssfi
    syl2anc
    #
    ad2antrr
    @63
    @65
    @69
    wcel
    #
    wa
    #
    @65
    @63
    @69
    cn
    @65
    @69
    cn
    wss
    @63
    @68
    vx
    cn
    ssrab2
    #
    a1i
    sselda
    #
    nnred
    @76
    @65
    @76
    @65
    @78
    nnnn0d
    nn0ge0d
    @63
    @68
    vx
    cn
    @64
    @63
    @64
    @57
    @6
    csn
    #
    cun
    #
    cn
    @14
    cB
    @6
    df-tp
    #
    @63
    @57
    @79
    cn
    wph
    @57
    cn
    wss
    #
    @55
    @62
    wph
    @18
    @13
    @82
    @20
    perfectlem.2
    @14
    cB
    cn
    prssi
    syl2anc
    #
    ad2antrr
    @63
    @6
    cn
    wph
    @54
    @7
    @62
    simplrl
    #
    snssd
    unssd
    syl5eqss
    #
    @63
    @67
    @64
    wcel
    #
    @68
    @86
    @67
    @14
    wceq
    #
    @67
    cB
    wceq
    #
    vx
    vn
    weq
    #
    w3o
    @63
    @68
    @67
    @14
    cB
    @6
    eltpi
    @63
    @87
    @68
    @88
    @89
    wph
    @87
    @68
    wi
    @55
    @62
    wph
    @68
    @87
    @14
    cB
    cdvds
    wbr
    wph
    @14
    @3
    @14
    cmul
    co
    #
    cB
    cdvds
    wph
    @3
    cz
    wcel
    @14
    cz
    wcel
    @14
    @90
    cdvds
    wbr
    wph
    @3
    wph
    @16
    @17
    @18
    @19
    simp2d
    #
    nnzd
    wph
    @14
    @20
    nnzd
    @3
    @14
    dvdsmul2
    syl2anc
    wph
    cB
    @3
    @47
    wph
    @3
    @91
    nncnd
    #
    wph
    @3
    @91
    nnne0d
    #
    divcan2d
    breqtrd
    @67
    @14
    cB
    cdvds
    breq1
    syl5ibrcom
    #
    ad2antrr
    wph
    @88
    @68
    wi
    @55
    @62
    wph
    @68
    @88
    cB
    cB
    cdvds
    wbr
    #
    wph
    cB
    cz
    wcel
    #
    @95
    wph
    cB
    perfectlem.2
    nnzd
    #
    cB
    iddvds
    syl
    @67
    cB
    cB
    cdvds
    breq1
    syl5ibrcom
    #
    ad2antrr
    @63
    @68
    @89
    @7
    wph
    @54
    @7
    @62
    simplrr
    @67
    @6
    cB
    cdvds
    breq1
    syl5ibrcom
    3jaod
    syl5
    imp
    ssrabdv
    fsumless
    @63
    @66
    @57
    @65
    vk
    csu
    #
    @79
    @65
    vk
    csu
    #
    caddc
    co
    @60
    @63
    @57
    @79
    @65
    @64
    vk
    @63
    @62
    @57
    @79
    cin
    c0
    wceq
    @56
    @62
    simpr
    @57
    @6
    disjsn
    sylibr
    @64
    @80
    wceq
    @63
    @81
    a1i
    @64
    cfn
    wcel
    @63
    @14
    cB
    @6
    tpfi
    a1i
    @63
    @65
    @64
    wcel
    wa
    @65
    @63
    @64
    cn
    @65
    @85
    sselda
    nncnd
    fsumsplit
    @63
    @99
    @59
    @100
    @6
    caddc
    wph
    @99
    @59
    wceq
    @55
    @62
    wph
    @14
    csn
    #
    @65
    vk
    csu
    #
    cB
    csn
    #
    @65
    vk
    csu
    #
    caddc
    co
    @14
    cB
    caddc
    co
    #
    @99
    @59
    wph
    @102
    @14
    @104
    cB
    caddc
    wph
    @18
    @14
    cc
    wcel
    @102
    @14
    wceq
    @20
    wph
    @14
    @20
    nncnd
    @65
    @14
    vk
    @14
    cn
    @65
    @14
    wceq
    id
    sumsn
    syl2anc
    wph
    @13
    cB
    cc
    wcel
    @104
    cB
    wceq
    perfectlem.2
    @47
    @65
    cB
    vk
    cB
    cn
    @65
    cB
    wceq
    id
    sumsn
    syl2anc
    oveq12d
    wph
    @101
    @103
    @65
    @57
    vk
    wph
    @101
    @103
    cin
    @103
    @101
    cin
    #
    c0
    @103
    @101
    incom
    wph
    cB
    @14
    wne
    @106
    c0
    wceq
    wph
    @14
    cB
    @21
    @48
    gtned
    cB
    @14
    disjsn2
    syl
    syl5eqr
    @57
    @101
    @103
    cun
    wceq
    wph
    @14
    cB
    df-pr
    a1i
    @57
    cfn
    wcel
    wph
    @14
    cB
    prfi
    a1i
    wph
    @65
    @57
    wcel
    wa
    @65
    wph
    @57
    cn
    @65
    @83
    sselda
    nncnd
    fsumsplit
    wph
    cB
    @3
    cB
    cmul
    co
    #
    caddc
    co
    #
    @3
    cdiv
    co
    #
    @14
    @107
    @3
    cdiv
    co
    #
    caddc
    co
    @59
    @105
    wph
    cB
    @107
    @3
    @47
    wph
    @3
    cB
    @92
    @47
    mulcld
    @92
    @93
    divdird
    wph
    @109
    @2
    cB
    cmul
    co
    #
    @3
    cdiv
    co
    #
    @59
    wph
    @108
    @111
    @3
    cdiv
    wph
    @108
    cB
    @111
    cB
    cmin
    co
    #
    caddc
    co
    @111
    wph
    @107
    @113
    cB
    caddc
    wph
    @107
    @111
    c1
    cB
    cmul
    co
    #
    cmin
    co
    @113
    wph
    @2
    c1
    cB
    wph
    @2
    @39
    nncnd
    #
    wph
    1cnd
    #
    @47
    subdird
    wph
    @114
    cB
    @111
    cmin
    wph
    cB
    @47
    mulid2d
    oveq2d
    eqtrd
    oveq2d
    wph
    cB
    @111
    @47
    wph
    @2
    cB
    @115
    @47
    mulcld
    pncan3d
    eqtrd
    oveq1d
    wph
    @2
    cB
    @3
    @115
    @47
    @92
    @93
    divassd
    #
    eqtrd
    wph
    @110
    cB
    @14
    caddc
    wph
    cB
    @3
    @47
    @92
    @93
    divcan3d
    oveq2d
    3eqtr3d
    3eqtr4d
    #
    ad2antrr
    @63
    @6
    cc
    wcel
    #
    @119
    @100
    @6
    wceq
    @63
    @6
    @84
    nncnd
    #
    @120
    @65
    @6
    vk
    @6
    cc
    vk
    vn
    weq
    id
    sumsn
    syl2anc
    oveq12d
    eqtrd
    wph
    @70
    @59
    wceq
    #
    @55
    @62
    wph
    @59
    c1
    cB
    csgm
    co
    #
    @69
    @65
    c1
    ccxp
    co
    #
    vk
    csu
    #
    @70
    wph
    @112
    @3
    @122
    cmul
    co
    #
    @3
    cdiv
    co
    @59
    @122
    wph
    @111
    @125
    @3
    cdiv
    wph
    @111
    c2
    c2
    cA
    cexp
    co
    #
    cmul
    co
    #
    cB
    cmul
    co
    c2
    @126
    cB
    cmul
    co
    #
    cmul
    co
    #
    @125
    wph
    @2
    @127
    cB
    cmul
    wph
    @2
    @126
    c2
    cmul
    co
    #
    @127
    wph
    @28
    cA
    cn0
    wcel
    #
    @2
    @130
    wceq
    2cn
    wph
    cA
    perfectlem.1
    nnnn0d
    #
    c2
    cA
    expp1
    sylancr
    wph
    @126
    cc
    wcel
    @28
    @130
    @127
    wceq
    wph
    @126
    wph
    c2
    cn
    wcel
    @131
    @126
    cn
    wcel
    #
    2nn
    @132
    c2
    cA
    nnexpcl
    sylancr
    #
    nncnd
    #
    2cn
    @126
    c2
    mulcom
    sylancl
    eqtrd
    oveq1d
    wph
    c2
    @126
    cB
    wph
    2cnd
    @135
    @47
    mulassd
    wph
    c1
    @128
    csgm
    co
    #
    c1
    @126
    csgm
    co
    #
    @122
    cmul
    co
    #
    @129
    @125
    wph
    @36
    @133
    @13
    @126
    cB
    cgcd
    co
    c1
    wceq
    #
    @136
    @138
    wceq
    @116
    @134
    perfectlem.2
    wph
    c2
    cB
    cgcd
    co
    c1
    wceq
    #
    @139
    wph
    c2
    cB
    cdvds
    wbr
    wn
    #
    @140
    perfectlem.3
    wph
    c2
    cprime
    wcel
    @96
    @141
    @140
    wb
    2prm
    @97
    c2
    cB
    coprm
    sylancr
    mpbid
    wph
    c2
    cz
    wcel
    #
    @96
    @131
    @140
    @139
    wi
    @142
    wph
    2z
    a1i
    @97
    @132
    c2
    cB
    cA
    rpexp1i
    syl3anc
    mpd
    c1
    @126
    cB
    sgmmul
    syl13anc
    perfectlem.4
    wph
    @137
    @3
    @122
    cmul
    wph
    c1
    c2
    @1
    c1
    cmin
    co
    #
    cexp
    co
    #
    csgm
    co
    #
    @137
    @3
    wph
    @144
    @126
    c1
    csgm
    wph
    @143
    cA
    c2
    cexp
    wph
    @37
    @36
    @143
    cA
    wceq
    @38
    ax-1cn
    cA
    c1
    pncan
    sylancl
    oveq2d
    oveq2d
    wph
    @46
    @145
    @3
    wceq
    @32
    @1
    1sgm2ppw
    syl
    eqtr3d
    oveq1d
    3eqtr3d
    3eqtrd
    oveq1d
    @117
    wph
    @122
    @3
    wph
    @122
    wph
    c1
    cn0
    wcel
    @13
    @122
    cn
    wcel
    1nn0
    perfectlem.2
    c1
    cB
    sgmnncl
    sylancr
    nncnd
    @92
    @93
    divcan3d
    3eqtr3d
    wph
    @36
    @13
    @122
    @124
    wceq
    ax-1cn
    perfectlem.2
    c1
    cB
    vk
    vx
    sgmval
    sylancr
    wph
    @69
    @123
    @65
    vk
    wph
    @75
    wa
    #
    @65
    @146
    @65
    @146
    @69
    cn
    @65
    @77
    wph
    @75
    simpr
    sseldi
    #
    nncnd
    cxp1d
    sumeq2dv
    3eqtrrd
    #
    ad2antrr
    3brtr3d
    @63
    @59
    @60
    clt
    wbr
    @61
    wn
    @63
    @59
    @6
    wph
    @59
    cr
    wcel
    #
    @55
    @62
    wph
    @2
    @14
    @40
    @21
    remulcld
    #
    ad2antrr
    #
    @63
    @6
    @84
    nnrpd
    ltaddrpd
    @63
    @59
    @60
    @151
    @63
    @59
    @6
    @151
    @63
    @6
    @84
    nnred
    readdcld
    ltnled
    mpbid
    condan
    @6
    @14
    cB
    elpri
    syl
    expr
    ralrimiva
    #
    wph
    @11
    @52
    vn
    cn
    wph
    @10
    @51
    @7
    wph
    @8
    @50
    @9
    wph
    c1
    @14
    @6
    wph
    c1
    cB
    wne
    #
    c1
    @14
    wceq
    #
    wph
    cB
    c1
    wph
    c1
    cB
    @15
    @49
    gtned
    necomd
    #
    wph
    @154
    c1
    cB
    wph
    @154
    c1
    cB
    wceq
    #
    wph
    c1
    cn
    wcel
    #
    @53
    c1
    cB
    cdvds
    wbr
    #
    @154
    @156
    wo
    #
    @157
    wph
    1nn
    a1i
    @152
    wph
    @96
    @158
    @97
    cB
    1dvds
    syl
    #
    @52
    @158
    @159
    wi
    vn
    c1
    cn
    @8
    @7
    @158
    @51
    @159
    @6
    c1
    cB
    cdvds
    breq1
    @8
    @50
    @154
    @9
    @156
    @6
    c1
    @14
    eqeq1
    @6
    c1
    cB
    eqeq1
    orbi12d
    imbi12d
    rspcv
    syl3c
    ord
    necon1ad
    mpd
    eqeq2d
    orbi1d
    imbi2d
    ralbidv
    mpbird
    vn
    cB
    isprm2
    sylanbrc
    wph
    @59
    c1
    caddc
    co
    #
    @59
    cle
    wbr
    #
    wn
    #
    @4
    wph
    @59
    @161
    clt
    wbr
    @163
    wph
    @59
    @150
    ltp1d
    wph
    @59
    @161
    @150
    wph
    @149
    @161
    cr
    wcel
    @150
    @59
    peano2re
    syl
    ltnled
    mpbid
    wph
    @162
    cB
    @3
    wph
    cB
    @3
    wne
    #
    @162
    wph
    @164
    wa
    #
    @14
    cB
    c1
    ctp
    #
    @65
    vk
    csu
    #
    @70
    @161
    @59
    cle
    wph
    @167
    @70
    cle
    wbr
    @164
    wph
    @69
    @65
    @166
    vk
    @74
    @146
    @65
    @147
    nnred
    @146
    @65
    @146
    @65
    @147
    nnnn0d
    nn0ge0d
    wph
    @68
    vx
    cn
    @166
    wph
    @166
    @57
    c1
    csn
    #
    cun
    #
    cn
    @14
    cB
    c1
    df-tp
    #
    wph
    @57
    @168
    cn
    @83
    @157
    @168
    cn
    wss
    wph
    1nn
    c1
    cn
    snssi
    mp1i
    unssd
    syl5eqss
    #
    wph
    @67
    @166
    wcel
    #
    @68
    @172
    @87
    @88
    @67
    c1
    wceq
    #
    w3o
    wph
    @68
    @67
    @14
    cB
    c1
    eltpi
    wph
    @87
    @68
    @88
    @173
    @94
    @98
    wph
    @68
    @173
    @158
    @160
    @67
    c1
    cB
    cdvds
    breq1
    syl5ibrcom
    3jaod
    syl5
    imp
    ssrabdv
    fsumless
    adantr
    @165
    @167
    @99
    @168
    @65
    vk
    csu
    #
    caddc
    co
    #
    @161
    @165
    @57
    @168
    @65
    @166
    vk
    @165
    c1
    @57
    wcel
    wn
    @57
    @168
    cin
    c0
    wceq
    @165
    c1
    @14
    cB
    @165
    @14
    c1
    wph
    @14
    c1
    wne
    @164
    wph
    @14
    c1
    cB
    @3
    wph
    cB
    @3
    @47
    @92
    @93
    diveq1ad
    necon3bid
    biimpar
    necomd
    wph
    @153
    @164
    @155
    adantr
    nelprd
    @57
    c1
    disjsn
    sylibr
    @166
    @169
    wceq
    @165
    @170
    a1i
    @166
    cfn
    wcel
    @165
    @14
    cB
    c1
    tpfi
    a1i
    @165
    @65
    @166
    wcel
    wa
    @65
    @165
    @166
    cn
    @65
    wph
    @166
    cn
    wss
    @164
    @171
    adantr
    sselda
    nncnd
    fsumsplit
    wph
    @175
    @161
    wceq
    @164
    wph
    @99
    @59
    @174
    c1
    caddc
    @118
    wph
    @35
    @36
    @174
    c1
    wceq
    @15
    ax-1cn
    @65
    c1
    vk
    c1
    cr
    @65
    c1
    wceq
    id
    sumsn
    sylancl
    oveq12d
    adantr
    eqtrd
    wph
    @121
    @164
    @148
    adantr
    3brtr3d
    ex
    necon1bd
    mpd
    jca
end
