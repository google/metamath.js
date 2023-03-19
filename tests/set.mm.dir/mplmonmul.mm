include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt.mm"
include "co.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "crab.mm"
include "cfv.mm"
include "cmin.mm"
include "cof.mm"
include "cmulr.mm"
include "cgsu.mm"
include "caddc.mm"
include "eqid.mm"
include "mplmon.mm"
include "mplmul.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "cbvmptv.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cres.mm"
include "simpr.mm"
include "snssd.mm"
include "resmptd.mm"
include "oveq2d.mm"
include "cmnd.mm"
include "cbs.mm"
include "crg.mm"
include "ad2antrr.mm"
include "ringmnd.mm"
include "syl.mm"
include "iftrue.mm"
include "cur.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fvmpt.mm"
include "ssrab2.mm"
include "simplr.mm"
include "psrbagconcl.mm"
include "syl3anc.mm"
include "sseldi.mm"
include "c0g.mm"
include "ifex.mm"
include "oveq12d.mm"
include "ringidcl.mm"
include "ring0cl.mm"
include "ifcld.mm"
include "ringlidm.mm"
include "syl2anc.mm"
include "wral.mm"
include "cn0.mm"
include "wb.mm"
include "wf.mm"
include "psrbagf.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "adantlr.mm"
include "cc.mm"
include "nn0cn.mm"
include "subadd.mm"
include "syl3an.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "ralbidva.mm"
include "mpteqb.mm"
include "ovexd.mm"
include "mprg.mm"
include "a1i.mm"
include "3bitr4g.mm"
include "feqmptd.mm"
include "offval2.mm"
include "eqeq12d.mm"
include "3bitr4d.mm"
include "3eqtrd.mm"
include "eqeltrrd.mm"
include "eqeltrd.mm"
include "fveq2.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "gsumsn.mm"
include "wn.mm"
include "c0.mm"
include "gsum0.mm"
include "cin.mm"
include "disjsn.mm"
include "wfn.mm"
include "mplelf.mm"
include "ffvelrnd.mm"
include "ringcl.mm"
include "fmptd.mm"
include "ffn.mm"
include "fnresdisj.mm"
include "3syl.mm"
include "biimpa.mm"
include "sylan2br.mm"
include "cr.mm"
include "nn0red.mm"
include "nn0addge1.mm"
include "ralrimiva.mm"
include "ofrfval2.mm"
include "mpbird.mm"
include "breq1.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "breq2.mm"
include "rabbidv.mm"
include "eleq2d.mm"
include "syl5ibrcom.mm"
include "con3dimp.mm"
include "iffalsed.mm"
include "3eqtr4a.mm"
include "pm2.61dan.mm"
include "cfn.mm"
include "ccmn.mm"
include "ringcmn.mm"
include "psrbaglefi.mm"
include "sylan.mm"
include "cdif.mm"
include "wss.mm"
include "ssdif.mm"
include "ax-mp.mm"
include "sseli.mm"
include "wne.mm"
include "eldifsni.mm"
include "adantl.mm"
include "neneqd.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cmap.mm"
include "ovex.mm"
include "rabex2.mm"
include "suppss2.mm"
include "suppssr.mm"
include "sylan2.mm"
include "oveq1d.mm"
include "eldifi.mm"
include "ringlz.mm"
include "eqtrd.mm"
include "rabex.mm"
include "wfun.mm"
include "w3a.mm"
include "csupp.mm"
include "cfsupp.mm"
include "mptrabex.mm"
include "funmpt.mm"
include "3pm3.2i.mm"
include "snfi.mm"
include "suppssfifsupp.mm"
include "syl12anc.mm"
include "gsumres.mm"
include "eqtr3d.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "eqtr4d.mm"

theorem mplmonmul
  let wph: wff ph
  let vy: setvar y
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let vf: setvar f
  let cI: class I
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vz: setvar z
  assume mplmon.s: |- P = ( I mPoly R )
  assume mplmon.b: |- B = ( Base ` P )
  assume mplmon.z: |- .0. = ( 0g ` R )
  assume mplmon.o: |- .1. = ( 1r ` R )
  assume mplmon.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume mplmon.i: |- ( ph -> I e. W )
  assume mplmon.r: |- ( ph -> R e. Ring )
  assume mplmon.x: |- ( ph -> X e. D )
  assume mplmonmul.t: |- .x. = ( .r ` P )
  assume mplmonmul.x: |- ( ph -> Y e. D )

  disjoint D y
  disjoint I f
  disjoint ph y
  disjoint f y
  disjoint X f
  disjoint X y
  disjoint .0. y
  disjoint .1. y
  disjoint R y
  disjoint Y f
  disjoint Y y
  disjoint j k
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint D j
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint D k
  disjoint x y
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D z
  disjoint f j
  disjoint f k
  disjoint f x
  disjoint f z
  disjoint I j
  disjoint I k
  disjoint I x
  disjoint I z
  disjoint j ph
  disjoint k ph
  disjoint ph z
  disjoint X j
  disjoint X k
  disjoint X x
  disjoint X z
  disjoint .0. j
  disjoint .0. k
  disjoint .1. j
  disjoint .1. k
  disjoint R j
  disjoint R k
  disjoint Y j
  disjoint Y k
  disjoint Y x
  disjoint Y z
  disjoint W x
  assert |- ( ph -> ( ( y e. D |-> if ( y = X , .1. , .0. ) ) .x. ( y e. D |-> if ( y = Y , .1. , .0. ) ) ) = ( y e. D |-> if ( y = ( X oF + Y ) , .1. , .0. ) ) )

  proof
    wph
    vy
    cD
    vy
    cv
    #
    cX
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    #
    vy
    cD
    @0
    cY
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    #
    c.x
    co
    vk
    cD
    cR
    vj
    vx
    cv
    #
    vk
    cv
    #
    cle
    cofr
    #
    wbr
    #
    vx
    cD
    crab
    #
    vj
    cv
    #
    @3
    cfv
    #
    @8
    @12
    cmin
    cof
    #
    co
    #
    @6
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    vy
    cD
    @0
    cX
    cY
    caddc
    cof
    co
    #
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    #
    wph
    vj
    vx
    cB
    cD
    cP
    cR
    c.x
    @17
    vf
    vk
    @3
    @6
    cI
    mplmon.s
    mplmon.b
    @17
    eqid
    #
    mplmonmul.t
    mplmon.d
    wph
    vy
    cB
    cD
    cP
    cR
    c.1
    vf
    cI
    cW
    cX
    c.0
    mplmon.s
    mplmon.b
    mplmon.z
    mplmon.o
    mplmon.d
    mplmon.i
    mplmon.r
    mplmon.x
    mplmon
    #
    wph
    vy
    cB
    cD
    cP
    cR
    c.1
    vf
    cI
    cW
    cY
    c.0
    mplmon.s
    mplmon.b
    mplmon.z
    mplmon.o
    mplmon.d
    mplmon.i
    mplmon.r
    mplmonmul.x
    mplmon
    #
    mplmul
    wph
    @25
    vk
    cD
    @8
    @22
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    @21
    vy
    vk
    cD
    @24
    @30
    @0
    @8
    wceq
    @23
    @29
    c.1
    c.0
    @0
    @8
    @22
    eqeq1
    ifbid
    cbvmptv
    wph
    vk
    cD
    @30
    @20
    wph
    @8
    cD
    wcel
    #
    wa
    #
    cR
    @19
    cX
    csn
    #
    cres
    #
    cgsu
    co
    #
    @30
    @20
    @32
    cX
    @11
    wcel
    #
    @35
    @30
    wceq
    @32
    @36
    wa
    #
    @35
    cR
    vj
    @33
    @18
    cmpt
    #
    cgsu
    co
    #
    cX
    @3
    cfv
    #
    @8
    cX
    @14
    co
    #
    @6
    cfv
    #
    @17
    co
    #
    @30
    @37
    @34
    @38
    cR
    cgsu
    @37
    vj
    @11
    @33
    @18
    @37
    cX
    @11
    @32
    @36
    simpr
    #
    snssd
    resmptd
    oveq2d
    @37
    cR
    cmnd
    wcel
    #
    cX
    cD
    wcel
    #
    @43
    cR
    cbs
    cfv
    #
    wcel
    @39
    @43
    wceq
    @37
    cR
    crg
    wcel
    #
    @45
    wph
    @48
    @31
    @36
    mplmon.r
    ad2antrr
    #
    cR
    ringmnd
    syl
    wph
    @46
    @31
    @36
    mplmon.x
    ad2antrr
    #
    @37
    @43
    @30
    @47
    @37
    @43
    c.1
    @41
    cY
    wceq
    #
    c.1
    c.0
    cif
    #
    @17
    co
    #
    @52
    @30
    @37
    @40
    c.1
    @42
    @52
    @17
    @37
    @46
    @40
    c.1
    wceq
    @50
    vy
    cX
    @2
    c.1
    cD
    @3
    @1
    c.1
    c.0
    iftrue
    @3
    eqid
    c.1
    cR
    cur
    cfv
    cvv
    mplmon.o
    cR
    cur
    fvex
    eqeltri
    #
    fvmpt
    syl
    @37
    @41
    cD
    wcel
    @42
    @52
    wceq
    @37
    @11
    cD
    @41
    @10
    vx
    cD
    ssrab2
    #
    @37
    cI
    cW
    wcel
    #
    @31
    @36
    @41
    @11
    wcel
    wph
    @56
    @31
    @36
    mplmon.i
    ad2antrr
    #
    wph
    @31
    @36
    simplr
    #
    @44
    vx
    cD
    @11
    vf
    @8
    cI
    cW
    cX
    mplmon.d
    @11
    eqid
    #
    psrbagconcl
    syl3anc
    sseldi
    vy
    @41
    @5
    @52
    cD
    @6
    @0
    @41
    wceq
    @4
    @51
    c.1
    c.0
    @0
    @41
    cY
    eqeq1
    ifbid
    @6
    eqid
    @51
    c.1
    c.0
    @54
    c.0
    cR
    c0g
    cfv
    cvv
    mplmon.z
    cR
    c0g
    fvex
    eqeltri
    #
    ifex
    fvmpt
    syl
    oveq12d
    @37
    @48
    @52
    @47
    wcel
    #
    @53
    @52
    wceq
    @49
    @37
    @48
    @61
    @49
    @48
    @51
    c.1
    c.0
    @47
    @47
    cR
    c.1
    @47
    eqid
    #
    mplmon.o
    ringidcl
    @47
    cR
    c.0
    @62
    mplmon.z
    ring0cl
    ifcld
    syl
    #
    @47
    cR
    @17
    c.1
    @52
    @62
    @26
    mplmon.o
    ringlidm
    syl2anc
    @37
    @51
    @29
    c.1
    c.0
    @37
    vz
    cI
    vz
    cv
    #
    @8
    cfv
    #
    @64
    cX
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    vz
    cI
    @64
    cY
    cfv
    #
    cmpt
    #
    wceq
    #
    vz
    cI
    @65
    cmpt
    #
    vz
    cI
    @66
    @69
    caddc
    co
    #
    cmpt
    #
    wceq
    #
    @51
    @29
    @37
    @67
    @69
    wceq
    #
    vz
    cI
    wral
    #
    @65
    @73
    wceq
    #
    vz
    cI
    wral
    #
    @71
    @75
    @37
    @76
    @78
    vz
    cI
    @37
    @64
    cI
    wcel
    #
    wa
    #
    @76
    @73
    @65
    wceq
    #
    @78
    @81
    @65
    cn0
    wcel
    #
    @66
    cn0
    wcel
    #
    @69
    cn0
    wcel
    #
    @76
    @82
    wb
    #
    @37
    cI
    cn0
    @64
    @8
    @37
    @56
    @31
    cI
    cn0
    @8
    wf
    @57
    @58
    cD
    vf
    @8
    cI
    cW
    mplmon.d
    psrbagf
    syl2anc
    #
    ffvelrnda
    #
    @32
    @80
    @84
    @36
    @32
    cI
    cn0
    @64
    cX
    @32
    @56
    @46
    cI
    cn0
    cX
    wf
    wph
    @56
    @31
    mplmon.i
    adantr
    #
    wph
    @46
    @31
    mplmon.x
    adantr
    #
    cD
    vf
    cX
    cI
    cW
    mplmon.d
    psrbagf
    syl2anc
    #
    ffvelrnda
    #
    adantlr
    #
    @32
    @80
    @85
    @36
    @32
    cI
    cn0
    @64
    cY
    wph
    cI
    cn0
    cY
    wf
    #
    @31
    wph
    @56
    cY
    cD
    wcel
    @94
    mplmon.i
    mplmonmul.x
    cD
    vf
    cY
    cI
    cW
    mplmon.d
    psrbagf
    syl2anc
    adantr
    #
    ffvelrnda
    #
    adantlr
    @83
    @65
    cc
    wcel
    @84
    @66
    cc
    wcel
    @85
    @69
    cc
    wcel
    @86
    @65
    nn0cn
    @66
    nn0cn
    @69
    nn0cn
    @65
    @66
    @69
    subadd
    syl3an
    syl3anc
    @73
    @65
    eqcom
    syl6bb
    ralbidva
    @67
    cvv
    wcel
    @71
    @77
    wb
    vz
    cI
    vz
    cI
    @67
    @69
    cvv
    mpteqb
    @80
    @65
    @66
    cmin
    ovexd
    mprg
    @65
    cvv
    wcel
    #
    @75
    @79
    wb
    vz
    cI
    vz
    cI
    @65
    @73
    cvv
    mpteqb
    @97
    @80
    @64
    @8
    fvex
    a1i
    mprg
    3bitr4g
    @37
    @41
    @68
    cY
    @70
    @37
    vz
    cI
    @65
    @66
    cmin
    @8
    cX
    cW
    cn0
    cn0
    @57
    @88
    @93
    @37
    vz
    cI
    cn0
    @8
    @87
    feqmptd
    #
    @32
    cX
    vz
    cI
    @66
    cmpt
    wceq
    @36
    @32
    vz
    cI
    cn0
    cX
    @91
    feqmptd
    #
    adantr
    offval2
    @32
    cY
    @70
    wceq
    @36
    @32
    vz
    cI
    cn0
    cY
    @95
    feqmptd
    #
    adantr
    eqeq12d
    @37
    @8
    @72
    @22
    @74
    @98
    @32
    @22
    @74
    wceq
    @36
    @32
    vz
    cI
    @66
    @69
    caddc
    cX
    cY
    cW
    cn0
    cn0
    @89
    @92
    @96
    @99
    @100
    offval2
    #
    adantr
    eqeq12d
    3bitr4d
    ifbid
    #
    3eqtrd
    #
    @37
    @52
    @30
    @47
    @102
    @63
    eqeltrrd
    eqeltrd
    @18
    @47
    @43
    vj
    cR
    cX
    cD
    @62
    @12
    cX
    wceq
    #
    @13
    @40
    @16
    @42
    @17
    @12
    cX
    @3
    fveq2
    @104
    @15
    @41
    @6
    @12
    cX
    @8
    @14
    oveq2
    fveq2d
    oveq12d
    gsumsn
    syl3anc
    @103
    3eqtrd
    @32
    @36
    wn
    #
    wa
    #
    cR
    c0
    cgsu
    co
    c.0
    @35
    @30
    cR
    c.0
    mplmon.z
    gsum0
    @106
    @34
    c0
    cR
    cgsu
    @105
    @32
    @11
    @33
    cin
    c0
    wceq
    #
    @34
    c0
    wceq
    #
    @11
    cX
    disjsn
    @32
    @107
    @108
    @32
    @11
    @47
    @19
    wf
    @19
    @11
    wfn
    @107
    @108
    wb
    @32
    vj
    @11
    @18
    @47
    @19
    @32
    @12
    @11
    wcel
    #
    wa
    #
    @48
    @13
    @47
    wcel
    @16
    @47
    wcel
    #
    @18
    @47
    wcel
    wph
    @48
    @31
    @109
    mplmon.r
    ad2antrr
    #
    @110
    cD
    @47
    @12
    @3
    wph
    cD
    @47
    @3
    wf
    #
    @31
    @109
    wph
    cB
    cD
    cP
    cR
    vf
    cI
    @47
    @3
    mplmon.s
    @62
    mplmon.b
    mplmon.d
    @27
    mplelf
    #
    ad2antrr
    @110
    @11
    cD
    @12
    @55
    @32
    @109
    simpr
    #
    sseldi
    ffvelrnd
    @110
    cD
    @47
    @15
    @6
    wph
    cD
    @47
    @6
    wf
    @31
    @109
    wph
    cB
    cD
    cP
    cR
    vf
    cI
    @47
    @6
    mplmon.s
    @62
    mplmon.b
    mplmon.d
    @28
    mplelf
    ad2antrr
    @110
    @11
    cD
    @15
    @55
    @110
    @56
    @31
    @109
    @15
    @11
    wcel
    wph
    @56
    @31
    @109
    mplmon.i
    ad2antrr
    wph
    @31
    @109
    simplr
    @115
    vx
    cD
    @11
    vf
    @8
    cI
    cW
    @12
    mplmon.d
    @59
    psrbagconcl
    syl3anc
    sseldi
    ffvelrnd
    #
    @47
    cR
    @17
    @13
    @16
    @62
    @26
    ringcl
    syl3anc
    @19
    eqid
    fmptd
    #
    @11
    @47
    @19
    ffn
    @11
    @33
    @19
    fnresdisj
    3syl
    biimpa
    sylan2br
    oveq2d
    @106
    @29
    c.1
    c.0
    @32
    @29
    @36
    @32
    @36
    @29
    cX
    @7
    @22
    @9
    wbr
    #
    vx
    cD
    crab
    #
    wcel
    #
    @32
    @46
    cX
    @22
    @9
    wbr
    #
    @120
    @90
    @32
    @121
    @66
    @73
    cle
    wbr
    #
    vz
    cI
    wral
    @32
    @122
    vz
    cI
    @32
    @80
    wa
    #
    @66
    cr
    wcel
    @85
    @122
    @123
    @66
    @92
    nn0red
    @96
    @66
    @69
    nn0addge1
    syl2anc
    ralrimiva
    @32
    vz
    cI
    @66
    @73
    cle
    cX
    @22
    cW
    cn0
    cvv
    @89
    @92
    @123
    @66
    @69
    caddc
    ovexd
    @99
    @101
    ofrfval2
    mpbird
    @118
    @121
    vx
    cX
    cD
    @7
    cX
    @22
    @9
    breq1
    elrab
    sylanbrc
    @29
    @11
    @119
    cX
    @29
    @10
    @118
    vx
    cD
    @8
    @22
    @7
    @9
    breq2
    rabbidv
    eleq2d
    syl5ibrcom
    con3dimp
    iffalsed
    3eqtr4a
    pm2.61dan
    @32
    @11
    @47
    @19
    cR
    cfn
    @33
    c.0
    @62
    mplmon.z
    @32
    @48
    cR
    ccmn
    wcel
    wph
    @48
    @31
    mplmon.r
    adantr
    cR
    ringcmn
    syl
    wph
    @56
    @31
    @11
    cfn
    wcel
    mplmon.i
    vx
    cD
    vf
    @8
    cI
    cW
    mplmon.d
    psrbaglefi
    sylan
    @117
    @32
    @11
    @18
    vj
    cvv
    @33
    c.0
    @32
    @12
    @11
    @33
    cdif
    #
    wcel
    #
    wa
    #
    @18
    c.0
    @16
    @17
    co
    #
    c.0
    @126
    @13
    c.0
    @16
    @17
    @125
    @32
    @12
    cD
    @33
    cdif
    #
    wcel
    @13
    c.0
    wceq
    @124
    @128
    @12
    @11
    cD
    wss
    @124
    @128
    wss
    @55
    @11
    cD
    @33
    ssdif
    ax-mp
    sseli
    @32
    cD
    @47
    cvv
    @3
    cvv
    @33
    @12
    c.0
    wph
    @113
    @31
    @114
    adantr
    @32
    cD
    @2
    vy
    cvv
    @33
    c.0
    @32
    @0
    @128
    wcel
    #
    wa
    #
    @1
    c.1
    c.0
    @130
    @0
    cX
    @129
    @0
    cX
    wne
    @32
    @0
    cD
    cX
    eldifsni
    adantl
    neneqd
    iffalsed
    cD
    cvv
    wcel
    @32
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vf
    cn0
    cI
    cmap
    co
    cD
    mplmon.d
    cn0
    cI
    cmap
    ovex
    rabex2
    #
    a1i
    #
    suppss2
    @132
    c.0
    cvv
    wcel
    #
    @32
    @60
    a1i
    suppssr
    sylan2
    oveq1d
    @125
    @32
    @109
    @127
    c.0
    wceq
    #
    @12
    @11
    @33
    eldifi
    @110
    @48
    @111
    @134
    @112
    @116
    @47
    cR
    @17
    @16
    c.0
    @62
    @26
    mplmon.z
    ringlz
    syl2anc
    sylan2
    eqtrd
    @11
    cvv
    wcel
    @32
    @10
    vx
    cD
    @131
    rabex
    a1i
    suppss2
    #
    @32
    @19
    cvv
    wcel
    #
    @19
    wfun
    #
    @133
    w3a
    #
    @33
    cfn
    wcel
    #
    @19
    c.0
    csupp
    co
    @33
    wss
    @19
    c.0
    cfsupp
    wbr
    @138
    @32
    @136
    @137
    @133
    @10
    vj
    vx
    cD
    @18
    @131
    mptrabex
    vj
    @11
    @18
    funmpt
    @60
    3pm3.2i
    a1i
    @139
    @32
    cX
    snfi
    a1i
    @135
    @33
    @19
    cvv
    cvv
    c.0
    suppssfifsupp
    syl12anc
    gsumres
    eqtr3d
    mpteq2dva
    syl5eq
    eqtr4d
end
