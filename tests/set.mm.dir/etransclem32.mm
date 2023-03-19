include "cdvn.mm"
include "co.mm"
include "cfv.mm"
include "cn0.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "csu.mm"
include "wceq.mm"
include "cmap.mm"
include "crab.mm"
include "cmpt.mm"
include "cfa.mm"
include "cprod.mm"
include "cdiv.mm"
include "cmul.mm"
include "etransclem11.mm"
include "etransclem30.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "etransclem12.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "adantlr.mm"
include "c1.mm"
include "cmin.mm"
include "cif.mm"
include "clt.mm"
include "wbr.mm"
include "wrex.mm"
include "caddc.mm"
include "cle.mm"
include "wn.mm"
include "wral.mm"
include "nfv.mm"
include "nfre1.mm"
include "nfn.mm"
include "nfan.mm"
include "cr.mm"
include "fzssre.mm"
include "wf.mm"
include "rabid.mm"
include "simplbi.mm"
include "elmapi.mm"
include "syl.mm"
include "adantl.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "cn.mm"
include "nnm1nn0.mm"
include "nn0red.mm"
include "nnred.mm"
include "ifcld.mm"
include "ad3antrrr.mm"
include "ralnex.mm"
include "biimpri.mm"
include "r19.21bi.mm"
include "adantll.mm"
include "nltled.mm"
include "ex.mm"
include "ralrimi.mm"
include "fveq2.mm"
include "cbvsumv.mm"
include "simprbi.mm"
include "syl5reqr.mm"
include "ad2antlr.mm"
include "fzfid.mm"
include "weq.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "breq12d.mm"
include "rspccva.mm"
include "fsumle.mm"
include "cuz.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "nnnn0d.mm"
include "nn0cnd.mm"
include "iftrue.mm"
include "fsum1p.mm"
include "0p1e1.mm"
include "oveq1i.mm"
include "a1i.mm"
include "sumeq1d.mm"
include "0red.mm"
include "1red.mm"
include "elfzelz.mm"
include "zred.mm"
include "0lt1.mm"
include "elfzle1.mm"
include "ltletrd.mm"
include "gt0ne0d.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "sumeq2dv.mm"
include "chash.mm"
include "cfn.mm"
include "cc.mm"
include "nncnd.mm"
include "fsumconst.mm"
include "syl2anc.mm"
include "hashfz1.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "oveq2d.mm"
include "nn0mulcld.mm"
include "addcomd.mm"
include "ad2antrr.mm"
include "breqtrd.mm"
include "syl5eqbr.mm"
include "eqbrtrd.mm"
include "syldan.mm"
include "nn0addcld.mm"
include "ltnled.mm"
include "mpbid.mm"
include "condan.mm"
include "w3a.mm"
include "nfcv.mm"
include "nfsum1.mm"
include "nfeq1.mm"
include "nfrab.mm"
include "nfcri.mm"
include "nf3an.mm"
include "cpr.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "cexp.mm"
include "etransclem5.mm"
include "eqtri.mm"
include "ffvelrnd.mm"
include "adantllr.mm"
include "elfznn0.mm"
include "etransclem20.mm"
include "simpllr.mm"
include "3ad2antl1.mm"
include "fveq12d.mm"
include "fveq1d.mm"
include "simp2.mm"
include "3ad2ant1.mm"
include "cz.mm"
include "fzssz.mm"
include "3adant3.mm"
include "simp3.mm"
include "etransclem19.mm"
include "eqidd.mm"
include "simp1lr.mm"
include "fvmptd.mm"
include "fprod0.mm"
include "rexlimdv3a.mm"
include "mpd.mm"
include "faccld.mm"
include "simpll.mm"
include "syl21anc.mm"
include "fprodcl.mm"
include "nnne0d.mm"
include "fprodn0.mm"
include "divcld.mm"
include "mul01d.mm"
include "wss.mm"
include "wo.mm"
include "eqid.mm"
include "etransclem16.mm"
include "olcd.mm"
include "sumz.mm"
include "mpteq2dva.mm"

theorem etransclem32
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cS: class S
  let vj: setvar j
  let cF: class F
  let cH: class H
  let cM: class M
  let cN: class N
  let cX: class X
  let cA: class A
  let vc: setvar c
  let vk: setvar k
  let vn: setvar n
  let vd: setvar d
  let vm: setvar m
  let vh: setvar h
  let vy: setvar y
  assume etransclem32.s: |- ( ph -> S e. { RR , CC } )
  assume etransclem32.x: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume etransclem32.p: |- ( ph -> P e. NN )
  assume etransclem32.m: |- ( ph -> M e. NN0 )
  assume etransclem32.f: |- F = ( x e. X |-> ( ( x ^ ( P - 1 ) ) x. prod_ j e. ( 1 ... M ) ( ( x - j ) ^ P ) ) )
  assume etransclem32.n: |- ( ph -> N e. NN0 )
  assume etransclem32.ngt: |- ( ph -> ( ( M x. P ) + ( P - 1 ) ) < N )
  assume etransclem32.h: |- H = ( j e. ( 0 ... M ) |-> ( x e. X |-> ( ( x - j ) ^ if ( j = 0 , ( P - 1 ) , P ) ) ) )

  disjoint H j
  disjoint H x
  disjoint j x
  disjoint M j
  disjoint M x
  disjoint N j
  disjoint N x
  disjoint P j
  disjoint P x
  disjoint S j
  disjoint S x
  disjoint X j
  disjoint X x
  disjoint j ph
  disjoint ph x
  disjoint A c
  disjoint H c
  disjoint H k
  disjoint H n
  disjoint c j
  disjoint c k
  disjoint c n
  disjoint c x
  disjoint j k
  disjoint j n
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint M c
  disjoint M d
  disjoint M k
  disjoint M m
  disjoint M n
  disjoint c d
  disjoint c m
  disjoint d j
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint j m
  disjoint k m
  disjoint m n
  disjoint M h
  disjoint M y
  disjoint c h
  disjoint c y
  disjoint h j
  disjoint h k
  disjoint h x
  disjoint h y
  disjoint j y
  disjoint k y
  disjoint x y
  disjoint N c
  disjoint N d
  disjoint N k
  disjoint N m
  disjoint N n
  disjoint N h
  disjoint N y
  disjoint P h
  disjoint P k
  disjoint P y
  disjoint S c
  disjoint S k
  disjoint S n
  disjoint S y
  disjoint X c
  disjoint X h
  disjoint X k
  disjoint X y
  disjoint X n
  disjoint c ph
  disjoint h ph
  disjoint k ph
  disjoint ph y
  disjoint m ph
  disjoint n ph
  disjoint k x
  assert |- ( ph -> ( ( S Dn F ) ` N ) = ( x e. X |-> 0 ) )

  proof
    wph
    cN
    cS
    cF
    cdvn
    co
    cfv
    vx
    cX
    cN
    vm
    cn0
    cc0
    cM
    cfz
    co
    #
    vk
    cv
    #
    vd
    cv
    cfv
    vk
    csu
    vm
    cv
    #
    wceq
    vd
    cc0
    @2
    cfz
    co
    @0
    cmap
    co
    crab
    cmpt
    #
    cfv
    #
    cN
    cfa
    cfv
    #
    @0
    vj
    cv
    #
    vc
    cv
    #
    cfv
    #
    cfa
    cfv
    #
    vj
    cprod
    #
    cdiv
    co
    #
    @0
    vx
    cv
    #
    @8
    cS
    @6
    cH
    cfv
    #
    cdvn
    co
    #
    cfv
    #
    cfv
    #
    vj
    cprod
    #
    cmul
    co
    #
    vc
    csu
    #
    cmpt
    vx
    cX
    cc0
    cmpt
    wph
    vx
    @3
    cP
    cS
    vj
    vn
    cF
    cH
    cM
    cN
    cX
    vc
    etransclem32.s
    etransclem32.x
    etransclem32.p
    etransclem32.m
    etransclem32.f
    etransclem32.n
    etransclem32.h
    vk
    vj
    vn
    vm
    cM
    vd
    vc
    etransclem11
    #
    etransclem30
    wph
    vx
    cX
    @19
    cc0
    wph
    @12
    cX
    wcel
    #
    wa
    #
    @19
    @4
    cc0
    vc
    csu
    #
    cc0
    @22
    @4
    @18
    cc0
    vc
    @22
    @7
    @4
    wcel
    #
    wa
    #
    @18
    @11
    cc0
    cmul
    co
    #
    cc0
    @25
    @17
    cc0
    @11
    cmul
    @22
    @24
    @7
    @0
    @8
    vj
    csu
    #
    cN
    wceq
    #
    vc
    cc0
    cN
    cfz
    co
    #
    @0
    cmap
    co
    #
    crab
    #
    wcel
    #
    @17
    cc0
    wceq
    #
    wph
    @24
    @32
    @21
    wph
    @24
    wa
    #
    @7
    @4
    @31
    wph
    @24
    simpr
    wph
    @4
    @31
    wceq
    @24
    wph
    @3
    vj
    vn
    cM
    cN
    vc
    @20
    etransclem32.n
    etransclem12
    adantr
    eleqtrd
    #
    adantlr
    @22
    @32
    wa
    #
    @1
    cc0
    wceq
    #
    cP
    c1
    cmin
    co
    #
    cP
    cif
    #
    @1
    @7
    cfv
    #
    clt
    wbr
    #
    vk
    @0
    wrex
    #
    @33
    wph
    @32
    @42
    @21
    wph
    @32
    wa
    #
    @42
    cN
    cM
    cP
    cmul
    co
    #
    @38
    caddc
    co
    #
    cle
    wbr
    #
    @43
    @42
    wn
    #
    @40
    @39
    cle
    wbr
    #
    vk
    @0
    wral
    #
    @46
    @43
    @47
    wa
    #
    @48
    vk
    @0
    @43
    @47
    vk
    @43
    vk
    nfv
    @42
    vk
    @41
    vk
    @0
    nfre1
    nfn
    nfan
    @50
    @1
    @0
    wcel
    #
    @48
    @50
    @51
    wa
    @40
    @39
    @43
    @51
    @40
    cr
    wcel
    @47
    @43
    @51
    wa
    #
    @29
    cr
    @40
    cc0
    cN
    fzssre
    #
    @43
    @0
    @29
    @1
    @7
    @32
    @0
    @29
    @7
    wf
    #
    wph
    @32
    @7
    @30
    wcel
    #
    @54
    @32
    @55
    @28
    @28
    vc
    @30
    rabid
    #
    simplbi
    @7
    @29
    @0
    elmapi
    syl
    #
    adantl
    #
    ffvelrnda
    #
    sseldi
    adantlr
    wph
    @39
    cr
    wcel
    @32
    @47
    @51
    wph
    @37
    @38
    cP
    cr
    wph
    @38
    wph
    cP
    cn
    wcel
    #
    @38
    cn0
    wcel
    etransclem32.p
    cP
    nnm1nn0
    syl
    #
    nn0red
    #
    wph
    cP
    etransclem32.p
    nnred
    #
    ifcld
    ad3antrrr
    @47
    @51
    @41
    wn
    #
    @43
    @47
    @64
    vk
    @0
    @64
    vk
    @0
    wral
    @47
    @41
    vk
    @0
    ralnex
    biimpri
    r19.21bi
    adantll
    nltled
    ex
    ralrimi
    @43
    @49
    wa
    #
    cN
    @0
    @40
    vk
    csu
    #
    @45
    cle
    @32
    cN
    @66
    wceq
    wph
    @49
    @32
    @66
    @27
    cN
    @0
    @8
    @40
    vj
    vk
    @6
    @1
    @7
    fveq2
    #
    cbvsumv
    @32
    @55
    @28
    @56
    simprbi
    syl5reqr
    ad2antlr
    @65
    @66
    @0
    vh
    cv
    #
    @7
    cfv
    #
    vh
    csu
    #
    @45
    cle
    @0
    @40
    @69
    vk
    vh
    @1
    @68
    @7
    fveq2
    #
    cbvsumv
    @65
    @70
    @0
    @68
    cc0
    wceq
    #
    @38
    cP
    cif
    #
    vh
    csu
    #
    @45
    cle
    @65
    @0
    @69
    @73
    vh
    @65
    cc0
    cM
    fzfid
    @43
    @68
    @0
    wcel
    #
    @69
    cr
    wcel
    @49
    @43
    @75
    wa
    @29
    cr
    @69
    @53
    @43
    @0
    @29
    @68
    @7
    @58
    ffvelrnda
    sseldi
    adantlr
    wph
    @73
    cr
    wcel
    @32
    @49
    @75
    wph
    @72
    @38
    cP
    cr
    @62
    @63
    ifcld
    ad3antrrr
    @49
    @75
    @69
    @73
    cle
    wbr
    #
    @43
    @48
    @76
    vk
    @68
    @0
    vk
    vh
    weq
    #
    @40
    @69
    @39
    @73
    cle
    @71
    @77
    @37
    @72
    @38
    cP
    @1
    @68
    cc0
    eqeq1
    ifbid
    breq12d
    rspccva
    adantll
    fsumle
    wph
    @74
    @45
    wceq
    @32
    @49
    wph
    @74
    @38
    cc0
    c1
    caddc
    co
    #
    cM
    cfz
    co
    #
    @73
    vh
    csu
    #
    caddc
    co
    @38
    @44
    caddc
    co
    @45
    wph
    @73
    @38
    vh
    cc0
    cM
    wph
    cM
    cn0
    cc0
    cuz
    cfv
    etransclem32.m
    nn0uz
    syl6eleq
    wph
    @75
    wa
    @73
    wph
    @73
    cn0
    wcel
    @75
    wph
    @72
    @38
    cP
    cn0
    @61
    wph
    cP
    etransclem32.p
    nnnn0d
    #
    ifcld
    adantr
    nn0cnd
    @72
    @38
    cP
    iftrue
    fsum1p
    wph
    @80
    @44
    @38
    caddc
    wph
    @80
    c1
    cM
    cfz
    co
    #
    @73
    vh
    csu
    @82
    cP
    vh
    csu
    #
    @44
    wph
    @79
    @82
    @73
    vh
    @79
    @82
    wceq
    wph
    @78
    c1
    cM
    cfz
    0p1e1
    oveq1i
    a1i
    sumeq1d
    wph
    @82
    @73
    cP
    vh
    @68
    @82
    wcel
    #
    @73
    cP
    wceq
    wph
    @84
    @72
    @38
    cP
    @84
    @68
    cc0
    @84
    @68
    @84
    cc0
    c1
    @68
    @84
    0red
    @84
    1red
    @84
    @68
    @68
    c1
    cM
    elfzelz
    zred
    cc0
    c1
    clt
    wbr
    @84
    0lt1
    a1i
    @68
    c1
    cM
    elfzle1
    ltletrd
    gt0ne0d
    neneqd
    iffalsed
    adantl
    sumeq2dv
    wph
    @83
    @82
    chash
    cfv
    #
    cP
    cmul
    co
    #
    @44
    wph
    @82
    cfn
    wcel
    cP
    cc
    wcel
    @83
    @86
    wceq
    wph
    c1
    cM
    fzfid
    wph
    cP
    etransclem32.p
    nncnd
    @82
    cP
    vh
    fsumconst
    syl2anc
    wph
    @85
    cM
    cP
    cmul
    wph
    cM
    cn0
    wcel
    @85
    cM
    wceq
    etransclem32.m
    cM
    hashfz1
    syl
    oveq1d
    eqtrd
    3eqtrd
    oveq2d
    wph
    @38
    @44
    wph
    @38
    @61
    nn0cnd
    wph
    @44
    wph
    cM
    cP
    etransclem32.m
    @81
    nn0mulcld
    #
    nn0cnd
    addcomd
    3eqtrd
    ad2antrr
    breqtrd
    syl5eqbr
    eqbrtrd
    syldan
    wph
    @46
    wn
    #
    @32
    @47
    wph
    @45
    cN
    clt
    wbr
    @88
    etransclem32.ngt
    wph
    @45
    cN
    wph
    @45
    wph
    @44
    @38
    @87
    @61
    nn0addcld
    nn0red
    wph
    cN
    etransclem32.n
    nn0red
    ltnled
    mpbid
    ad2antrr
    condan
    adantlr
    @36
    @41
    @33
    vk
    @0
    @36
    @51
    @41
    w3a
    #
    @0
    @16
    @12
    @40
    cS
    @1
    cH
    cfv
    #
    cdvn
    co
    #
    cfv
    #
    cfv
    #
    vj
    @1
    @36
    @51
    @41
    vj
    @22
    @32
    vj
    @22
    vj
    nfv
    vj
    vc
    @31
    @28
    vj
    vc
    @30
    vj
    @27
    cN
    @0
    @8
    vj
    vj
    @0
    nfcv
    nfsum1
    nfeq1
    vj
    @30
    nfcv
    nfrab
    nfcri
    nfan
    @51
    vj
    nfv
    @41
    vj
    nfv
    nf3an
    vj
    @93
    nfcv
    @89
    cc0
    cM
    fzfid
    @36
    @51
    @6
    @0
    wcel
    #
    @16
    cc
    wcel
    @41
    @36
    @94
    wa
    #
    cX
    cc
    @12
    @15
    @95
    vy
    cP
    cS
    vk
    cH
    @6
    cM
    @8
    cX
    wph
    cS
    cr
    cc
    cpr
    wcel
    #
    @21
    @32
    @94
    etransclem32.s
    ad3antrrr
    wph
    cX
    ccnfld
    ctopn
    cfv
    cS
    crest
    co
    wcel
    #
    @21
    @32
    @94
    etransclem32.x
    ad3antrrr
    wph
    @60
    @21
    @32
    @94
    etransclem32.p
    ad3antrrr
    cH
    vj
    @0
    vx
    cX
    @12
    @6
    cmin
    co
    @6
    cc0
    wceq
    @38
    cP
    cif
    cexp
    co
    cmpt
    cmpt
    #
    vk
    @0
    vy
    cX
    vy
    cv
    #
    @1
    cmin
    co
    @39
    cexp
    co
    cmpt
    cmpt
    etransclem32.h
    vx
    vy
    cP
    vj
    vk
    cM
    cX
    etransclem5
    eqtri
    @36
    @94
    simpr
    @95
    @8
    @29
    wcel
    #
    @8
    cn0
    wcel
    #
    wph
    @32
    @94
    @100
    @21
    @43
    @94
    wa
    @0
    @29
    @6
    @7
    @32
    @54
    wph
    @94
    @57
    ad2antlr
    @43
    @94
    simpr
    ffvelrnd
    #
    adantllr
    @8
    cN
    elfznn0
    #
    syl
    etransclem20
    wph
    @21
    @32
    @94
    simpllr
    ffvelrnd
    3ad2antl1
    vj
    vk
    weq
    #
    @12
    @15
    @92
    @104
    @8
    @40
    @14
    @91
    @104
    @13
    @90
    cS
    cdvn
    @6
    @1
    cH
    fveq2
    oveq2d
    @67
    fveq12d
    fveq1d
    @36
    @51
    @41
    simp2
    #
    @89
    vy
    @12
    cc0
    cc0
    cX
    @92
    cr
    @89
    vy
    cP
    cS
    vh
    cH
    @1
    cM
    @40
    cX
    @36
    @51
    @96
    @41
    wph
    @96
    @21
    @32
    etransclem32.s
    ad2antrr
    3ad2ant1
    @36
    @51
    @97
    @41
    wph
    @97
    @21
    @32
    etransclem32.x
    ad2antrr
    3ad2ant1
    @36
    @51
    @60
    @41
    wph
    @60
    @21
    @32
    etransclem32.p
    ad2antrr
    3ad2ant1
    cH
    @98
    vh
    @0
    vy
    cX
    @99
    @68
    cmin
    co
    @73
    cexp
    co
    cmpt
    cmpt
    etransclem32.h
    vx
    vy
    cP
    vj
    vh
    cM
    cX
    etransclem5
    eqtri
    @105
    @36
    @51
    @40
    cz
    wcel
    #
    @41
    wph
    @32
    @51
    @106
    @21
    @52
    @29
    cz
    @40
    cc0
    cN
    fzssz
    @59
    sseldi
    adantllr
    3adant3
    @36
    @51
    @41
    simp3
    etransclem19
    @89
    vy
    vx
    weq
    wa
    cc0
    eqidd
    wph
    @21
    @32
    @51
    @41
    simp1lr
    @89
    0red
    fvmptd
    fprod0
    rexlimdv3a
    mpd
    syldan
    oveq2d
    wph
    @24
    @26
    cc0
    wceq
    @21
    @34
    @11
    @34
    @5
    @10
    wph
    @5
    cc
    wcel
    @24
    wph
    @5
    wph
    cN
    etransclem32.n
    faccld
    nncnd
    adantr
    @34
    @0
    @9
    vj
    @34
    cc0
    cM
    fzfid
    #
    @34
    @94
    wa
    #
    @9
    @108
    @8
    @108
    @100
    @101
    @108
    wph
    @32
    @94
    @100
    wph
    @24
    @94
    simpll
    @34
    @32
    @94
    @35
    adantr
    @34
    @94
    simpr
    @102
    syl21anc
    @103
    syl
    faccld
    #
    nncnd
    #
    fprodcl
    @34
    @0
    @9
    vj
    @107
    @110
    @108
    @9
    @109
    nnne0d
    fprodn0
    divcld
    mul01d
    adantlr
    eqtrd
    sumeq2dv
    @22
    @4
    cA
    cuz
    cfv
    wss
    #
    @4
    cfn
    wcel
    #
    wo
    #
    @23
    cc0
    wceq
    wph
    @113
    @21
    wph
    @112
    @111
    wph
    @3
    vk
    vm
    cM
    cN
    vd
    @3
    eqid
    etransclem32.n
    etransclem16
    olcd
    adantr
    @4
    vc
    cA
    sumz
    syl
    eqtrd
    mpteq2dva
    eqtrd
end
