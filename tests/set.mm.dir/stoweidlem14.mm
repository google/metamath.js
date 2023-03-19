include "cv.mm"
include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "c2.mm"
include "cdiv.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "cle.mm"
include "wral.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "ssrab2.mm"
include "a1i.mm"
include "syl5eqss.mm"
include "cr.mm"
include "rprecred.mm"
include "arch.mm"
include "breq2.mm"
include "elrab.mm"
include "biimpri.mm"
include "syl6eleqr.mm"
include "simpr.mm"
include "jca.mm"
include "reximi2.mm"
include "rexn0.mm"
include "4syl.mm"
include "nnwo.mm"
include "syl2anc.mm"
include "df-rex.mm"
include "sylib.mm"
include "elrab2.mm"
include "simplbi.mm"
include "ad2antrl.mm"
include "simpl.mm"
include "simprl.mm"
include "simprr.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "nfv.mm"
include "cbvralf.mm"
include "simprbi.mm"
include "wb.mm"
include "cc0.mm"
include "1red.mm"
include "nnre.mm"
include "adantl.mm"
include "rpregt0d.mm"
include "adantr.mm"
include "ltdivmul2.mm"
include "syl3anc.mm"
include "syldan.mm"
include "mpbid.mm"
include "syl12anc.mm"
include "wceq.mm"
include "oveq1.mm"
include "cc.mm"
include "rpcnd.mm"
include "mulid2d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "rpred.mm"
include "rehalfcld.mm"
include "halfre.mm"
include "2re.mm"
include "2pos.mm"
include "ltdiv1.mm"
include "syl112anc.mm"
include "halflt1.mm"
include "lttrd.mm"
include "eqbrtrd.mm"
include "adantlr.mm"
include "wn.mm"
include "cuz.mm"
include "cfv.mm"
include "cmin.mm"
include "simpll.mm"
include "simplrl.mm"
include "syl.mm"
include "neqne.mm"
include "eluz2b3.mm"
include "sylanbrc.mm"
include "peano2rem.mm"
include "ad2antrr.mm"
include "rpne0d.mm"
include "rereccld.mm"
include "cz.mm"
include "1zzd.mm"
include "w3a.mm"
include "caddc.mm"
include "df-2.mm"
include "fveq2i.mm"
include "eleq2i.mm"
include "eluzsub.mm"
include "syl3an3b.mm"
include "nnuz.mm"
include "wo.mm"
include "wi.mm"
include "ltm1d.mm"
include "ltnle.mm"
include "notbid.mm"
include "rspcev.mm"
include "rexnal.mm"
include "ex.mm"
include "imnan.mm"
include "con2i.mm"
include "ad2antlr.mm"
include "sylnib.mm"
include "ianor.mm"
include "imor.mm"
include "sylibr.mm"
include "mpd.mm"
include "nltled.mm"
include "eluzelre.mm"
include "remulcld.mm"
include "3adant3.mm"
include "readdcld.mm"
include "eluzelcn.mm"
include "mulcld.mm"
include "3ad2ant1.mm"
include "npcand.mm"
include "resubcld.mm"
include "simp3.mm"
include "3ad2ant2.mm"
include "lemul1.mm"
include "1cnd.mm"
include "subdird.mm"
include "oveq2d.mm"
include "3jca.mm"
include "divcan1.mm"
include "3brtr3d.mm"
include "leadd1dd.mm"
include "eqbrtrrd.mm"
include "pm3.2i.mm"
include "lediv1.mm"
include "ltadd2dd.mm"
include "1p1e2.mm"
include "syl6breq.mm"
include "2div2e1.mm"
include "lelttrd.mm"
include "pm2.61dan.mm"
include "jca32.mm"
include "eximdv.mm"

theorem stoweidlem14
  let wph: wff ph
  let cA: class A
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let vz: setvar z
  let vx: setvar x
  assume stoweidlem14.1: |- A = { j e. NN | ( 1 / D ) < j }
  assume stoweidlem14.2: |- ( ph -> D e. RR+ )
  assume stoweidlem14.3: |- ( ph -> D < 1 )

  disjoint j k
  disjoint D j
  disjoint D k
  disjoint A k
  disjoint k ph
  disjoint j z
  disjoint k z
  disjoint A z
  disjoint k x
  assert |- ( ph -> E. k e. NN ( 1 < ( k x. D ) /\ ( ( k x. D ) / 2 ) < 1 ) )

  proof
    wph
    vk
    cv
    #
    cn
    wcel
    #
    c1
    @0
    cD
    cmul
    co
    #
    clt
    wbr
    #
    @2
    c2
    cdiv
    co
    #
    c1
    clt
    wbr
    #
    wa
    #
    wa
    #
    vk
    wex
    #
    @6
    vk
    cn
    wrex
    wph
    @0
    cA
    wcel
    #
    @0
    vz
    cv
    #
    cle
    wbr
    #
    vz
    cA
    wral
    #
    wa
    #
    vk
    wex
    #
    @8
    wph
    @12
    vk
    cA
    wrex
    #
    @14
    wph
    cA
    cn
    wss
    cA
    c0
    wne
    #
    @15
    wph
    cA
    c1
    cD
    cdiv
    co
    #
    vj
    cv
    #
    clt
    wbr
    #
    vj
    cn
    crab
    #
    cn
    stoweidlem14.1
    @20
    cn
    wss
    wph
    @19
    vj
    cn
    ssrab2
    a1i
    syl5eqss
    wph
    @17
    cr
    wcel
    #
    @17
    @0
    clt
    wbr
    #
    vk
    cn
    wrex
    @22
    vk
    cA
    wrex
    @16
    wph
    cD
    stoweidlem14.2
    rprecred
    #
    @17
    vk
    arch
    @22
    @22
    vk
    cn
    cA
    @1
    @22
    wa
    #
    @9
    @22
    @24
    @0
    @20
    cA
    @0
    @20
    wcel
    @24
    @19
    @22
    vj
    @0
    cn
    @18
    @0
    @17
    clt
    breq2
    #
    elrab
    biimpri
    stoweidlem14.1
    syl6eleqr
    @1
    @22
    simpr
    jca
    reximi2
    @22
    vk
    cA
    rexn0
    4syl
    vk
    vz
    cA
    nnwo
    syl2anc
    @12
    vk
    cA
    df-rex
    sylib
    wph
    @13
    @7
    vk
    wph
    @13
    @7
    wph
    @13
    wa
    #
    @1
    @3
    @5
    @9
    @1
    wph
    @12
    @9
    @1
    @22
    @19
    @22
    vj
    @0
    cn
    cA
    @25
    stoweidlem14.1
    elrab2
    #
    simplbi
    #
    ad2antrl
    @26
    wph
    @9
    @0
    @18
    cle
    wbr
    #
    vj
    cA
    wral
    #
    @3
    wph
    @13
    simpl
    wph
    @9
    @12
    simprl
    @26
    @12
    @30
    wph
    @9
    @12
    simprr
    @11
    @29
    vz
    vj
    cA
    vz
    cA
    nfcv
    vj
    cA
    @20
    stoweidlem14.1
    @19
    vj
    cn
    nfrab1
    nfcxfr
    @11
    vj
    nfv
    @29
    vz
    nfv
    @10
    @18
    @0
    cle
    breq2
    cbvralf
    sylib
    wph
    @9
    @30
    wa
    #
    wa
    @22
    @3
    @9
    @22
    wph
    @30
    @9
    @1
    @22
    @27
    simprbi
    ad2antrl
    wph
    @31
    @1
    @22
    @3
    wb
    #
    @9
    @1
    wph
    @30
    @28
    ad2antrl
    wph
    @1
    wa
    #
    c1
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    cD
    cr
    wcel
    #
    cc0
    cD
    clt
    wbr
    wa
    #
    @32
    @33
    1red
    @1
    @35
    wph
    @0
    nnre
    #
    adantl
    wph
    @37
    @1
    wph
    cD
    stoweidlem14.2
    rpregt0d
    #
    adantr
    c1
    @0
    cD
    ltdivmul2
    syl3anc
    syldan
    mpbid
    syl12anc
    @26
    @0
    c1
    wceq
    #
    @5
    wph
    @40
    @5
    @13
    wph
    @40
    wa
    #
    @4
    cD
    c2
    cdiv
    co
    #
    c1
    clt
    @41
    @2
    cD
    c2
    cdiv
    @41
    @2
    c1
    cD
    cmul
    co
    #
    cD
    @40
    @2
    @43
    wceq
    wph
    @0
    c1
    cD
    cmul
    oveq1
    adantl
    @41
    cD
    wph
    cD
    cc
    wcel
    #
    @40
    wph
    cD
    stoweidlem14.2
    rpcnd
    #
    adantr
    mulid2d
    eqtrd
    oveq1d
    wph
    @42
    c1
    clt
    wbr
    @40
    wph
    @42
    c1
    c2
    cdiv
    co
    #
    c1
    wph
    cD
    wph
    cD
    stoweidlem14.2
    rpred
    #
    rehalfcld
    @46
    cr
    wcel
    wph
    halfre
    a1i
    wph
    1red
    #
    wph
    cD
    c1
    clt
    wbr
    #
    @42
    @46
    clt
    wbr
    #
    stoweidlem14.3
    wph
    @36
    @34
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    @49
    @50
    wb
    @47
    @48
    @51
    wph
    2re
    a1i
    #
    @52
    wph
    2pos
    a1i
    #
    cD
    c1
    c2
    ltdiv1
    syl112anc
    mpbid
    @46
    c1
    clt
    wbr
    wph
    halflt1
    a1i
    lttrd
    adantr
    eqbrtrd
    adantlr
    @26
    @40
    wn
    #
    wa
    #
    wph
    @0
    c2
    cuz
    cfv
    #
    wcel
    #
    @0
    c1
    cmin
    co
    #
    @17
    cle
    wbr
    #
    @5
    wph
    @13
    @55
    simpll
    @56
    @1
    @0
    c1
    wne
    #
    @58
    @56
    @9
    @1
    wph
    @9
    @12
    @55
    simplrl
    #
    @28
    syl
    @55
    @61
    @26
    @0
    c1
    neqne
    adantl
    @0
    eluz2b3
    sylanbrc
    #
    @56
    @59
    @17
    @56
    @9
    @1
    @35
    @59
    cr
    wcel
    #
    @62
    @28
    @38
    @0
    peano2rem
    #
    4syl
    @56
    cD
    wph
    @36
    @13
    @55
    @47
    ad2antrr
    wph
    cD
    cc0
    wne
    #
    @13
    @55
    wph
    cD
    stoweidlem14.2
    rpne0d
    #
    ad2antrr
    rereccld
    @56
    @59
    cn
    wcel
    #
    @17
    @59
    clt
    wbr
    #
    wn
    #
    @56
    c1
    cz
    wcel
    #
    @71
    @58
    @68
    @56
    1zzd
    #
    @72
    @63
    @71
    @71
    @58
    w3a
    @59
    c1
    cuz
    cfv
    #
    cn
    @58
    @71
    @71
    @0
    c1
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    @59
    @73
    wcel
    @57
    @75
    @0
    c2
    @74
    cuz
    df-2
    fveq2i
    eleq2i
    c1
    c1
    @0
    eluzsub
    syl3an3b
    nnuz
    syl6eleqr
    syl3anc
    @56
    @68
    wn
    @70
    wo
    #
    @68
    @70
    wi
    @56
    @68
    @69
    wa
    #
    wn
    @76
    @56
    @59
    cA
    wcel
    #
    @77
    @13
    @78
    wn
    wph
    @55
    @78
    @13
    @78
    @9
    @12
    wn
    #
    wi
    @13
    wn
    @78
    @9
    @79
    @78
    @9
    wa
    #
    @11
    wn
    #
    vz
    cA
    wrex
    #
    @79
    @78
    @9
    @0
    @59
    cle
    wbr
    #
    wn
    #
    @82
    @80
    @64
    @35
    @84
    @80
    @35
    @64
    @9
    @35
    @78
    @9
    @1
    @35
    @28
    @38
    syl
    adantl
    #
    @65
    syl
    @85
    @64
    @35
    wa
    #
    @59
    @0
    clt
    wbr
    @84
    @86
    @0
    @64
    @35
    simpr
    ltm1d
    @59
    @0
    ltnle
    mpbid
    syl2anc
    @81
    @84
    vz
    @59
    cA
    @10
    @59
    wceq
    @11
    @83
    @10
    @59
    @0
    cle
    breq2
    notbid
    rspcev
    syldan
    @11
    vz
    cA
    rexnal
    sylib
    ex
    @9
    @12
    imnan
    sylib
    con2i
    ad2antlr
    @19
    @69
    vj
    @59
    cn
    cA
    @18
    @59
    @17
    clt
    breq2
    stoweidlem14.1
    elrab2
    sylnib
    @68
    @69
    ianor
    sylib
    @68
    @70
    imor
    sylibr
    mpd
    nltled
    wph
    @58
    @60
    w3a
    #
    @4
    c1
    cD
    caddc
    co
    #
    c2
    cdiv
    co
    #
    c1
    wph
    @58
    @4
    cr
    wcel
    @60
    wph
    @58
    wa
    #
    @2
    @90
    @0
    cD
    @58
    @35
    wph
    c2
    @0
    eluzelre
    #
    adantl
    wph
    @36
    @58
    @47
    adantr
    #
    remulcld
    #
    rehalfcld
    3adant3
    wph
    @58
    @89
    cr
    wcel
    @60
    @90
    @88
    wph
    @88
    cr
    wcel
    #
    @58
    wph
    c1
    cD
    @48
    @47
    readdcld
    #
    adantr
    rehalfcld
    3adant3
    @87
    1red
    #
    @87
    @2
    @88
    cle
    wbr
    #
    @4
    @89
    cle
    wbr
    #
    @87
    @2
    cD
    cmin
    co
    #
    cD
    caddc
    co
    @2
    @88
    cle
    @87
    @2
    cD
    wph
    @58
    @2
    cc
    wcel
    @60
    @90
    @0
    cD
    @58
    @0
    cc
    wcel
    wph
    c2
    @0
    eluzelcn
    adantl
    #
    wph
    @44
    @58
    @45
    adantr
    #
    mulcld
    3adant3
    wph
    @58
    @44
    @60
    @45
    3ad2ant1
    npcand
    @87
    @99
    c1
    cD
    wph
    @58
    @99
    cr
    wcel
    @60
    @90
    @2
    cD
    @93
    @92
    resubcld
    3adant3
    @96
    wph
    @58
    @36
    @60
    @47
    3ad2ant1
    @87
    @59
    cD
    cmul
    co
    #
    @17
    cD
    cmul
    co
    #
    @99
    c1
    cle
    @87
    @60
    @102
    @103
    cle
    wbr
    #
    wph
    @58
    @60
    simp3
    @87
    @64
    @21
    @37
    @60
    @104
    wb
    @58
    wph
    @64
    @60
    @58
    @0
    c1
    @91
    @58
    1red
    resubcld
    3ad2ant2
    wph
    @58
    @21
    @60
    @23
    3ad2ant1
    wph
    @58
    @37
    @60
    @39
    3ad2ant1
    @59
    @17
    cD
    lemul1
    syl3anc
    mpbid
    wph
    @58
    @102
    @99
    wceq
    @60
    @90
    @102
    @2
    @43
    cmin
    co
    @99
    @90
    @0
    c1
    cD
    @100
    @90
    1cnd
    @101
    subdird
    @90
    @43
    cD
    @2
    cmin
    @90
    cD
    @101
    mulid2d
    oveq2d
    eqtrd
    3adant3
    @87
    c1
    cc
    wcel
    #
    @44
    @66
    w3a
    #
    @103
    c1
    wceq
    wph
    @58
    @106
    @60
    wph
    @105
    @44
    @66
    wph
    1cnd
    @45
    @67
    3jca
    3ad2ant1
    c1
    cD
    divcan1
    syl
    3brtr3d
    leadd1dd
    eqbrtrrd
    @87
    @2
    cr
    wcel
    #
    @94
    @51
    @52
    wa
    #
    @97
    @98
    wb
    wph
    @58
    @107
    @60
    @93
    3adant3
    wph
    @58
    @94
    @60
    @95
    3ad2ant1
    @108
    @87
    @51
    @52
    2re
    2pos
    pm3.2i
    a1i
    @2
    @88
    c2
    lediv1
    syl3anc
    mpbid
    wph
    @58
    @89
    c1
    clt
    wbr
    @60
    wph
    @89
    c2
    c2
    cdiv
    co
    #
    c1
    clt
    wph
    @88
    c2
    clt
    wbr
    #
    @89
    @109
    clt
    wbr
    #
    wph
    @88
    @74
    c2
    clt
    wph
    cD
    c1
    c1
    @47
    @48
    @48
    stoweidlem14.3
    ltadd2dd
    1p1e2
    syl6breq
    wph
    @94
    @51
    @51
    @52
    @110
    @111
    wb
    @95
    @53
    @53
    @54
    @88
    c2
    c2
    ltdiv1
    syl112anc
    mpbid
    2div2e1
    syl6breq
    3ad2ant1
    lelttrd
    syl3anc
    pm2.61dan
    jca32
    ex
    eximdv
    mpd
    @6
    vk
    cn
    df-rex
    sylibr
end
