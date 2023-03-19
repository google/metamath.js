include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cppi.mm"
include "cfv.mm"
include "clog.mm"
include "cmul.mm"
include "ccht.mm"
include "clt.mm"
include "rpred.mm"
include "recnd.mm"
include "sqvald.mm"
include "oveq1d.mm"
include "cr.mm"
include "wcel.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "cico.mm"
include "wa.mm"
include "wb.mm"
include "2re.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "sylib.mm"
include "simpld.mm"
include "ppicl.mm"
include "syl.mm"
include "nn0red.mm"
include "cc0.mm"
include "0red.mm"
include "a1i.mm"
include "2pos.mm"
include "simprd.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "relogcld.mm"
include "mul4d.mm"
include "eqtrd.mm"
include "ccxp.mm"
include "cmin.mm"
include "remulcld.mm"
include "rpcxpcld.mm"
include "resubcld.mm"
include "chtcl.mm"
include "c1.mm"
include "1red.mm"
include "1lt2.mm"
include "rplogcld.mm"
include "rpmulcld.mm"
include "cdiv.mm"
include "cn.mm"
include "ppinncl.mm"
include "nndivred.mm"
include "ltsub13d.mm"
include "cc.mm"
include "wne.mm"
include "wceq.mm"
include "nnrpd.mm"
include "rpcnne0d.mm"
include "divsubdir.mm"
include "syl3anc.mm"
include "divid.mm"
include "breqtrrd.mm"
include "ltmuldivd.mm"
include "mpbird.mm"
include "crp.mm"
include "ppiltx.mm"
include "ltsub2dd.mm"
include "lttrd.mm"
include "ltmul1dd.mm"
include "cfl.mm"
include "caddc.mm"
include "cfz.mm"
include "cprime.mm"
include "cin.mm"
include "cv.mm"
include "csu.mm"
include "cfn.mm"
include "wss.mm"
include "fzfid.mm"
include "inss1.mm"
include "ssfi.mm"
include "sylancl.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "prmnn.mm"
include "fsumrecl.mm"
include "chash.mm"
include "fsumconst.mm"
include "syl2anc.mm"
include "ppifl.mm"
include "oveq12d.mm"
include "cuz.mm"
include "ltled.mm"
include "wi.mm"
include "1re.mm"
include "ltle.mm"
include "mpd.mm"
include "cxplead.mm"
include "cxp1d.mm"
include "breqtrd.mm"
include "flword2.mm"
include "ppidif.mm"
include "eqtr3d.mm"
include "eqtr4d.mm"
include "adantr.mm"
include "ce.mm"
include "reflcl.mm"
include "peano2re.mm"
include "3syl.mm"
include "fllep1.mm"
include "elfzle1.mm"
include "letrd.mm"
include "rpne0d.mm"
include "cxpefd.mm"
include "eqcomd.mm"
include "reeflogd.mm"
include "3brtr4d.mm"
include "efle.mm"
include "fsumle.mm"
include "eqbrtrrd.mm"
include "prmuz2.mm"
include "eluz2b2.mm"
include "nnred.mm"
include "rpge0d.mm"
include "flge0nn0.mm"
include "nn0p1nn.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "fzss1.mm"
include "ssrin.mm"
include "fsumless.mm"
include "cicc.mm"
include "chtval.mm"
include "2eluzge1.mm"
include "ppisval2.mm"
include "sumeq1d.mm"
include "eqbrtrd.mm"

theorem chtppilimlem1
  let wph: wff ph
  let cA: class A
  let cN: class N
  let vp: setvar p
  let vx: setvar x
  let vz: setvar z
  assume chtppilim.1: |- ( ph -> A e. RR+ )
  assume chtppilim.2: |- ( ph -> A < 1 )
  assume chtppilim.3: |- ( ph -> N e. ( 2 [,) +oo ) )
  assume chtppilim.4: |- ( ph -> ( ( N ^c A ) / ( ppi ` N ) ) < ( 1 - A ) )


  assert |- ( ph -> ( ( A ^ 2 ) x. ( ( ppi ` N ) x. ( log ` N ) ) ) < ( theta ` N ) )

  proof
    wph
    cA
    c2
    cexp
    co
    #
    cN
    cppi
    cfv
    #
    cN
    clog
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    cA
    @1
    cmul
    co
    #
    cA
    @2
    cmul
    co
    #
    cmul
    co
    #
    cN
    ccht
    cfv
    #
    clt
    wph
    @4
    cA
    cA
    cmul
    co
    #
    @3
    cmul
    co
    @7
    wph
    @0
    @9
    @3
    cmul
    wph
    cA
    wph
    cA
    wph
    cA
    chtppilim.1
    rpred
    #
    recnd
    #
    sqvald
    oveq1d
    wph
    cA
    cA
    @1
    @2
    @11
    @11
    wph
    @1
    wph
    @1
    wph
    cN
    cr
    wcel
    #
    @1
    cn0
    wcel
    wph
    @12
    c2
    cN
    cle
    wbr
    #
    wph
    cN
    c2
    cpnf
    cico
    co
    wcel
    #
    @12
    @13
    wa
    #
    chtppilim.3
    c2
    cr
    wcel
    #
    @14
    @15
    wb
    2re
    c2
    cN
    elicopnf
    ax-mp
    sylib
    #
    simpld
    #
    cN
    ppicl
    syl
    nn0red
    #
    recnd
    #
    wph
    @2
    wph
    cN
    wph
    cN
    @18
    wph
    cc0
    c2
    cN
    wph
    0red
    @16
    wph
    2re
    a1i
    #
    @18
    cc0
    c2
    clt
    wbr
    wph
    2pos
    a1i
    wph
    @12
    @13
    @17
    simprd
    #
    ltletrd
    elrpd
    #
    relogcld
    #
    recnd
    mul4d
    eqtrd
    wph
    @7
    @1
    cN
    cA
    ccxp
    co
    #
    cppi
    cfv
    #
    cmin
    co
    #
    @6
    cmul
    co
    #
    @8
    wph
    @5
    @6
    wph
    cA
    @1
    @10
    @19
    remulcld
    #
    wph
    cA
    @2
    @10
    @24
    remulcld
    #
    remulcld
    wph
    @27
    @6
    wph
    @1
    @26
    @19
    wph
    @26
    wph
    @25
    cr
    wcel
    #
    @26
    cn0
    wcel
    wph
    @25
    wph
    cN
    cA
    @23
    @10
    rpcxpcld
    #
    rpred
    #
    @25
    ppicl
    syl
    nn0red
    #
    resubcld
    #
    @30
    remulcld
    #
    wph
    @12
    @8
    cr
    wcel
    @18
    cN
    chtcl
    syl
    #
    wph
    @5
    @27
    @6
    @29
    @35
    wph
    cA
    @2
    chtppilim.1
    wph
    cN
    @18
    wph
    c1
    c2
    cN
    wph
    1red
    #
    @21
    @18
    c1
    c2
    clt
    wbr
    wph
    1lt2
    a1i
    @22
    ltletrd
    #
    rplogcld
    rpmulcld
    wph
    @5
    @1
    @25
    cmin
    co
    #
    @27
    @29
    wph
    @1
    @25
    @19
    @33
    resubcld
    #
    @35
    wph
    @5
    @40
    clt
    wbr
    cA
    @40
    @1
    cdiv
    co
    #
    clt
    wbr
    wph
    cA
    c1
    @25
    @1
    cdiv
    co
    #
    cmin
    co
    #
    @42
    clt
    wph
    @43
    c1
    cA
    wph
    @25
    @1
    @33
    wph
    @15
    @1
    cn
    wcel
    @17
    cN
    ppinncl
    syl
    #
    nndivred
    @38
    @10
    chtppilim.4
    ltsub13d
    wph
    @42
    @1
    @1
    cdiv
    co
    #
    @43
    cmin
    co
    #
    @44
    wph
    @1
    cc
    wcel
    #
    @25
    cc
    wcel
    @48
    @1
    cc0
    wne
    wa
    #
    @42
    @47
    wceq
    @20
    wph
    @25
    @33
    recnd
    wph
    @1
    wph
    @1
    @45
    nnrpd
    #
    rpcnne0d
    #
    @1
    @25
    @1
    divsubdir
    syl3anc
    wph
    @46
    c1
    @43
    cmin
    wph
    @49
    @46
    c1
    wceq
    @51
    @1
    divid
    syl
    oveq1d
    eqtrd
    breqtrrd
    wph
    cA
    @40
    @1
    @10
    @41
    @50
    ltmuldivd
    mpbird
    wph
    @26
    @25
    @1
    @34
    @33
    @19
    wph
    @25
    crp
    wcel
    @26
    @25
    clt
    wbr
    @32
    @25
    ppiltx
    syl
    ltsub2dd
    lttrd
    ltmul1dd
    wph
    @28
    @25
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cN
    cfl
    cfv
    #
    cfz
    co
    #
    cprime
    cin
    #
    vp
    cv
    #
    clog
    cfv
    #
    vp
    csu
    #
    @8
    @36
    wph
    @56
    @58
    vp
    wph
    @55
    cfn
    wcel
    @56
    @55
    wss
    @56
    cfn
    wcel
    #
    wph
    @53
    @54
    fzfid
    @55
    cprime
    inss1
    #
    @55
    @56
    ssfi
    sylancl
    #
    wph
    @57
    @56
    wcel
    #
    wa
    #
    @57
    @64
    @57
    cprime
    wcel
    #
    @57
    crp
    wcel
    @64
    @56
    cprime
    @57
    @55
    cprime
    inss2
    wph
    @63
    simpr
    #
    sseldi
    @65
    @57
    @57
    prmnn
    nnrpd
    syl
    #
    relogcld
    #
    fsumrecl
    @37
    wph
    @56
    @6
    vp
    csu
    #
    @28
    @59
    cle
    wph
    @69
    @56
    chash
    cfv
    #
    @6
    cmul
    co
    #
    @28
    wph
    @60
    @6
    cc
    wcel
    @69
    @71
    wceq
    @62
    wph
    @6
    @30
    recnd
    @56
    @6
    vp
    fsumconst
    syl2anc
    wph
    @27
    @70
    @6
    cmul
    wph
    @54
    cppi
    cfv
    #
    @52
    cppi
    cfv
    #
    cmin
    co
    #
    @27
    @70
    wph
    @72
    @1
    @73
    @26
    cmin
    wph
    @12
    @72
    @1
    wceq
    @18
    cN
    ppifl
    syl
    wph
    @31
    @73
    @26
    wceq
    @33
    @25
    ppifl
    syl
    oveq12d
    wph
    @54
    @52
    cuz
    cfv
    wcel
    #
    @74
    @70
    wceq
    wph
    @31
    @12
    @25
    cN
    cle
    wbr
    @75
    @33
    @18
    wph
    @25
    cN
    c1
    ccxp
    co
    cN
    cle
    wph
    cN
    cA
    c1
    @18
    wph
    c1
    cN
    @38
    @18
    @39
    ltled
    @10
    @38
    wph
    cA
    c1
    clt
    wbr
    #
    cA
    c1
    cle
    wbr
    #
    chtppilim.2
    wph
    cA
    cr
    wcel
    c1
    cr
    wcel
    @76
    @77
    wi
    @10
    1re
    cA
    c1
    ltle
    sylancl
    mpd
    cxplead
    wph
    cN
    wph
    cN
    @18
    recnd
    #
    cxp1d
    breqtrd
    @25
    cN
    flword2
    syl3anc
    @52
    @54
    ppidif
    syl
    eqtr3d
    oveq1d
    eqtr4d
    wph
    @56
    @6
    @58
    vp
    @62
    wph
    @6
    cr
    wcel
    #
    @63
    @30
    adantr
    #
    @68
    @64
    @6
    @58
    cle
    wbr
    #
    @6
    ce
    cfv
    #
    @58
    ce
    cfv
    #
    cle
    wbr
    #
    @64
    @25
    @57
    @82
    @83
    cle
    @64
    @25
    @53
    @57
    wph
    @31
    @63
    @33
    adantr
    wph
    @53
    cr
    wcel
    #
    @63
    wph
    @31
    @52
    cr
    wcel
    @85
    @33
    @25
    reflcl
    @52
    peano2re
    3syl
    adantr
    @64
    @57
    @67
    rpred
    wph
    @25
    @53
    cle
    wbr
    #
    @63
    wph
    @31
    @86
    @33
    @25
    fllep1
    syl
    adantr
    @64
    @57
    @55
    wcel
    @53
    @57
    cle
    wbr
    @64
    @56
    @55
    @57
    @61
    @66
    sseldi
    @57
    @53
    @54
    elfzle1
    syl
    letrd
    wph
    @82
    @25
    wceq
    @63
    wph
    @25
    @82
    wph
    cN
    cA
    @78
    wph
    cN
    @23
    rpne0d
    @11
    cxpefd
    eqcomd
    adantr
    @64
    @57
    @67
    reeflogd
    3brtr4d
    @64
    @79
    @58
    cr
    wcel
    @81
    @84
    wb
    @80
    @68
    @6
    @58
    efle
    syl2anc
    mpbird
    fsumle
    eqbrtrrd
    wph
    @59
    c1
    @54
    cfz
    co
    #
    cprime
    cin
    #
    @58
    vp
    csu
    #
    @8
    cle
    wph
    @88
    @58
    @56
    vp
    wph
    @87
    cfn
    wcel
    @88
    @87
    wss
    @88
    cfn
    wcel
    wph
    c1
    @54
    fzfid
    @87
    cprime
    inss1
    @87
    @88
    ssfi
    sylancl
    wph
    @57
    @88
    wcel
    #
    wa
    #
    @58
    @91
    @57
    @91
    @57
    @91
    @57
    cn
    wcel
    #
    c1
    @57
    clt
    wbr
    #
    @91
    @57
    c2
    cuz
    cfv
    wcel
    #
    @92
    @93
    wa
    @91
    @65
    @94
    @91
    @88
    cprime
    @57
    @87
    cprime
    inss2
    wph
    @90
    simpr
    sseldi
    @57
    prmuz2
    syl
    @57
    eluz2b2
    sylib
    #
    simpld
    nnred
    @91
    @92
    @93
    @95
    simprd
    rplogcld
    #
    rpred
    @91
    @58
    @96
    rpge0d
    wph
    @53
    c1
    cuz
    cfv
    #
    wcel
    @55
    @87
    wss
    @56
    @88
    wss
    wph
    @53
    cn
    @97
    wph
    @52
    cn0
    wcel
    #
    @53
    cn
    wcel
    wph
    @31
    cc0
    @25
    cle
    wbr
    @98
    @33
    wph
    @25
    @32
    rpge0d
    @25
    flge0nn0
    syl2anc
    @52
    nn0p1nn
    syl
    nnuz
    syl6eleq
    @53
    c1
    @54
    fzss1
    @55
    @87
    cprime
    ssrin
    3syl
    fsumless
    wph
    @8
    cc0
    cN
    cicc
    co
    cprime
    cin
    #
    @58
    vp
    csu
    #
    @89
    wph
    @12
    @8
    @100
    wceq
    @18
    cN
    vp
    chtval
    syl
    wph
    @99
    @88
    @58
    vp
    wph
    @12
    c2
    @97
    wcel
    @99
    @88
    wceq
    @18
    2eluzge1
    cN
    c1
    ppisval2
    sylancl
    sumeq1d
    eqtrd
    breqtrrd
    letrd
    ltletrd
    eqbrtrd
end
