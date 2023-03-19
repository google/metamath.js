include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cicc.mm"
include "cv.mm"
include "cexp.mm"
include "citg.mm"
include "cmin.mm"
include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "syl.mm"
include "nncnd.mm"
include "cc.mm"
include "wa.mm"
include "cr.mm"
include "wss.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "sselda.mm"
include "adantr.mm"
include "expcld.mm"
include "cmpt.mm"
include "ccncf.mm"
include "cibl.mm"
include "cres.mm"
include "resmptd.mm"
include "expcncf.mm"
include "rescncf.mm"
include "sylc.mm"
include "eqeltrrd.mm"
include "cniccibl.mm"
include "syl3anc.mm"
include "itgcl.mm"
include "nnne0d.mm"
include "cmul.mm"
include "itgmulc2.mm"
include "cioo.mm"
include "cfv.mm"
include "eqidd.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "adantl.mm"
include "simpr.mm"
include "ioossicc.mm"
include "a1i.mm"
include "syldan.mm"
include "mulcld.mm"
include "fvmptd.mm"
include "itgeq2dv.mm"
include "cdv.mm"
include "crn.mm"
include "ctg.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "1nn0.mm"
include "nn0addcld.mm"
include "nn0cnd.mm"
include "1cnd.mm"
include "addcld.mm"
include "wf.mm"
include "cdm.mm"
include "eqid.mm"
include "fmptd.mm"
include "ssid.mm"
include "dvexp.mm"
include "pncand.mm"
include "mpteq2dv.mm"
include "eqtrd.mm"
include "feq1d.mm"
include "mpbird.mm"
include "fdm.mm"
include "syl5sseqr.mm"
include "dvres3.mm"
include "syl22anc.mm"
include "reseq1d.mm"
include "resmpt.mm"
include "mp1i.mm"
include "3eqtr3d.mm"
include "tgioo2.mm"
include "cnt.mm"
include "iccntr.mm"
include "dvmptres2.mm"
include "ioossre.mm"
include "sstri.mm"
include "cncfmptc.mm"
include "mulcncf.mm"
include "eqeltrd.mm"
include "cvol.mm"
include "ioombl.mm"
include "iblss.mm"
include "ftc2.mm"
include "wral.mm"
include "fveq1d.mm"
include "ralrimivw.mm"
include "itgeq2.mm"
include "oveq1d.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "rexrd.mm"
include "ubicc2.mm"
include "recnd.mm"
include "lbicc2.mm"
include "oveq12d.mm"
include "itgioo.mm"
include "3eqtr3rd.mm"
include "mvllmuld.mm"

theorem itgpowd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cN: class N
  let vt: setvar t
  assume itgpowd.1: |- ( ph -> A e. RR )
  assume itgpowd.2: |- ( ph -> B e. RR )
  assume itgpowd.3: |- ( ph -> A <_ B )
  assume itgpowd.4: |- ( ph -> N e. NN0 )

  disjoint A x
  disjoint B x
  disjoint N x
  disjoint ph x
  disjoint A t
  disjoint t x
  disjoint B t
  disjoint N t
  disjoint ph t
  assert |- ( ph -> S. ( A [,] B ) ( x ^ N ) _d x = ( ( ( B ^ ( N + 1 ) ) - ( A ^ ( N + 1 ) ) ) / ( N + 1 ) ) )

  proof
    wph
    cN
    c1
    caddc
    co
    #
    vx
    cA
    cB
    cicc
    co
    #
    vx
    cv
    #
    cN
    cexp
    co
    #
    citg
    #
    cB
    @0
    cexp
    co
    #
    cA
    @0
    cexp
    co
    #
    cmin
    co
    #
    wph
    @0
    wph
    cN
    cn0
    wcel
    #
    @0
    cn
    wcel
    #
    itgpowd.4
    cN
    nn0p1nn
    syl
    #
    nncnd
    #
    wph
    vx
    @1
    @3
    cc
    wph
    @2
    @1
    wcel
    #
    wa
    #
    @2
    cN
    wph
    @1
    cc
    @2
    wph
    @1
    cr
    cc
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @1
    cr
    wss
    itgpowd.1
    itgpowd.2
    cA
    cB
    iccssre
    syl2anc
    #
    ax-resscn
    syl6ss
    #
    sselda
    wph
    @8
    @12
    itgpowd.4
    adantr
    expcld
    #
    wph
    @14
    @15
    vx
    @1
    @3
    cmpt
    #
    @1
    cc
    ccncf
    co
    #
    wcel
    @19
    cibl
    wcel
    itgpowd.1
    itgpowd.2
    wph
    vx
    cc
    @3
    cmpt
    #
    @1
    cres
    #
    @19
    @20
    wph
    vx
    cc
    @1
    @3
    @17
    resmptd
    wph
    @1
    cc
    wss
    #
    @21
    cc
    cc
    ccncf
    co
    #
    wcel
    #
    @22
    @20
    wcel
    @17
    wph
    @8
    @25
    itgpowd.4
    vx
    cN
    expcncf
    syl
    cc
    cc
    @1
    @21
    rescncf
    sylc
    eqeltrrd
    cA
    cB
    @19
    cniccibl
    syl3anc
    #
    itgcl
    wph
    @0
    @10
    nnne0d
    wph
    @0
    @4
    cmul
    co
    vx
    @1
    @0
    @3
    cmul
    co
    #
    citg
    #
    @7
    wph
    vx
    @1
    @3
    @0
    cc
    @11
    @18
    @26
    itgmulc2
    wph
    vx
    cA
    cB
    cioo
    co
    #
    @2
    vt
    @29
    @0
    vt
    cv
    #
    cN
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cfv
    #
    citg
    #
    vx
    @29
    @27
    citg
    @7
    @28
    wph
    vx
    @29
    @34
    @27
    wph
    @2
    @29
    wcel
    #
    wa
    #
    vt
    @2
    @32
    @27
    @29
    @33
    cc
    @37
    @33
    eqidd
    @30
    @2
    wceq
    #
    @32
    @27
    wceq
    @37
    @38
    @31
    @3
    @0
    cmul
    @30
    @2
    cN
    cexp
    oveq1
    oveq2d
    adantl
    wph
    @36
    simpr
    @37
    @0
    @3
    wph
    @0
    cc
    wcel
    #
    @36
    @11
    adantr
    wph
    @36
    @12
    @3
    cc
    wcel
    wph
    @29
    @1
    @2
    @29
    @1
    wss
    wph
    cA
    cB
    ioossicc
    a1i
    #
    sselda
    @18
    syldan
    mulcld
    fvmptd
    itgeq2dv
    wph
    vx
    @29
    @2
    cr
    vt
    @1
    @30
    @0
    cexp
    co
    #
    cmpt
    #
    cdv
    co
    #
    cfv
    #
    citg
    #
    cB
    @42
    cfv
    #
    cA
    @42
    cfv
    #
    cmin
    co
    @35
    @7
    wph
    vx
    cA
    cB
    @42
    itgpowd.1
    itgpowd.2
    itgpowd.3
    wph
    @43
    @33
    @29
    cc
    ccncf
    co
    #
    wph
    vt
    @41
    @32
    cr
    cioo
    crn
    ctg
    cfv
    #
    ccnfld
    ctopn
    cfv
    #
    cc
    cr
    @29
    @1
    cr
    cr
    cc
    cpr
    wcel
    #
    wph
    reelprrecn
    a1i
    #
    wph
    @30
    cr
    wcel
    #
    wa
    #
    @30
    @0
    wph
    cr
    cc
    @30
    cr
    cc
    wss
    #
    wph
    ax-resscn
    a1i
    sselda
    #
    wph
    @0
    cn0
    wcel
    #
    @53
    wph
    cN
    c1
    itgpowd.4
    c1
    cn0
    wcel
    wph
    1nn0
    a1i
    nn0addcld
    #
    adantr
    expcld
    @54
    @0
    @31
    @54
    cN
    c1
    wph
    cN
    cc
    wcel
    #
    @53
    wph
    cN
    itgpowd.4
    nn0cnd
    #
    adantr
    @54
    1cnd
    addcld
    @54
    @30
    cN
    @56
    wph
    @8
    @53
    itgpowd.4
    adantr
    expcld
    mulcld
    wph
    cr
    vt
    cc
    @41
    cmpt
    #
    cr
    cres
    #
    cdv
    co
    #
    vt
    cc
    @32
    cmpt
    #
    cr
    cres
    #
    cr
    vt
    cr
    @41
    cmpt
    #
    cdv
    co
    vt
    cr
    @32
    cmpt
    #
    wph
    @63
    cc
    @61
    cdv
    co
    #
    cr
    cres
    #
    @65
    wph
    @51
    cc
    cc
    @61
    wf
    cc
    cc
    wss
    #
    cr
    @68
    cdm
    #
    wss
    @63
    @69
    wceq
    @52
    wph
    vt
    cc
    @41
    cc
    @61
    wph
    @30
    cc
    wcel
    #
    wa
    #
    @30
    @0
    wph
    @72
    simpr
    #
    wph
    @57
    @72
    @58
    adantr
    expcld
    @61
    eqid
    fmptd
    @70
    wph
    cc
    ssid
    a1i
    #
    wph
    cc
    cr
    @71
    ax-resscn
    wph
    cc
    cc
    @68
    wf
    #
    @71
    cc
    wceq
    wph
    @76
    cc
    cc
    @64
    wf
    wph
    vt
    cc
    @32
    cc
    @64
    @73
    @0
    @31
    wph
    @39
    @72
    @11
    adantr
    @73
    @30
    cN
    @74
    wph
    @8
    @72
    itgpowd.4
    adantr
    expcld
    mulcld
    @64
    eqid
    fmptd
    wph
    cc
    cc
    @68
    @64
    wph
    @68
    vt
    cc
    @0
    @30
    @0
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    @64
    wph
    @9
    @68
    @80
    wceq
    @10
    vt
    @0
    dvexp
    syl
    wph
    vt
    cc
    @79
    @32
    wph
    @78
    @31
    @0
    cmul
    wph
    @77
    cN
    @30
    cexp
    wph
    cN
    c1
    @60
    wph
    1cnd
    pncand
    oveq2d
    oveq2d
    mpteq2dv
    eqtrd
    #
    feq1d
    mpbird
    cc
    cc
    @68
    fdm
    syl
    syl5sseqr
    cc
    cr
    @61
    dvres3
    syl22anc
    wph
    @68
    @64
    cr
    @81
    reseq1d
    eqtrd
    wph
    @62
    @66
    cr
    cdv
    @55
    @62
    @66
    wceq
    wph
    ax-resscn
    vt
    cc
    cr
    @41
    resmpt
    mp1i
    oveq2d
    @55
    @65
    @67
    wceq
    wph
    ax-resscn
    vt
    cc
    cr
    @32
    resmpt
    mp1i
    3eqtr3d
    @16
    @50
    @50
    eqid
    #
    tgioo2
    @82
    wph
    @14
    @15
    @1
    @49
    cnt
    cfv
    cfv
    @29
    wceq
    itgpowd.1
    itgpowd.2
    cA
    cB
    iccntr
    syl2anc
    dvmptres2
    #
    wph
    vt
    @0
    @31
    @29
    wph
    @39
    @29
    cc
    wss
    #
    @70
    vt
    @29
    @0
    cmpt
    @48
    wcel
    @11
    @84
    wph
    @29
    cr
    cc
    cA
    cB
    ioossre
    ax-resscn
    sstri
    #
    a1i
    #
    @75
    vt
    @0
    @29
    cc
    cncfmptc
    syl3anc
    wph
    vt
    cc
    @31
    cmpt
    #
    @29
    cres
    #
    vt
    @29
    @31
    cmpt
    #
    @48
    @84
    @88
    @89
    wceq
    wph
    @85
    vt
    cc
    @29
    @31
    resmpt
    mp1i
    wph
    @84
    @87
    @24
    wcel
    #
    @88
    @48
    wcel
    @86
    wph
    @8
    @90
    itgpowd.4
    vt
    cN
    expcncf
    syl
    #
    cc
    cc
    @29
    @87
    rescncf
    sylc
    eqeltrrd
    mulcncf
    eqeltrd
    wph
    @43
    @33
    cibl
    @83
    wph
    vt
    @29
    @1
    @32
    cc
    @40
    @29
    cvol
    cdm
    wcel
    wph
    cA
    cB
    ioombl
    a1i
    wph
    @30
    @1
    wcel
    #
    wa
    #
    @0
    @31
    @93
    cN
    c1
    wph
    @59
    @92
    @60
    adantr
    @93
    1cnd
    addcld
    @93
    @30
    cN
    wph
    @1
    cc
    @30
    @17
    sselda
    wph
    @8
    @92
    itgpowd.4
    adantr
    expcld
    mulcld
    wph
    @14
    @15
    vt
    @1
    @32
    cmpt
    #
    @20
    wcel
    @94
    cibl
    wcel
    itgpowd.1
    itgpowd.2
    wph
    vt
    @0
    @31
    @1
    wph
    @39
    @23
    @70
    vt
    @1
    @0
    cmpt
    @20
    wcel
    @11
    @17
    @75
    vt
    @0
    @1
    cc
    cncfmptc
    syl3anc
    wph
    @87
    @1
    cres
    #
    vt
    @1
    @31
    cmpt
    @20
    wph
    vt
    cc
    @1
    @31
    @17
    resmptd
    wph
    @23
    @90
    @95
    @20
    wcel
    @17
    @91
    cc
    cc
    @1
    @87
    rescncf
    sylc
    eqeltrrd
    mulcncf
    cA
    cB
    @94
    cniccibl
    syl3anc
    iblss
    eqeltrd
    wph
    @61
    @1
    cres
    #
    @42
    @20
    wph
    vt
    cc
    @1
    @41
    @17
    resmptd
    wph
    @23
    @61
    @24
    wcel
    #
    @96
    @20
    wcel
    @17
    wph
    @57
    @97
    @58
    vt
    @0
    expcncf
    syl
    cc
    cc
    @1
    @61
    rescncf
    sylc
    eqeltrrd
    ftc2
    wph
    @44
    @34
    wceq
    #
    vx
    @29
    wral
    @45
    @35
    wceq
    wph
    @98
    vx
    @29
    wph
    @2
    @43
    @33
    @83
    fveq1d
    ralrimivw
    vx
    @29
    @44
    @34
    itgeq2
    syl
    wph
    @46
    @5
    @47
    @6
    cmin
    wph
    vt
    cB
    @41
    @5
    @1
    @42
    cc
    wph
    @42
    eqidd
    #
    wph
    @30
    cB
    wceq
    #
    wa
    @30
    cB
    @0
    cexp
    wph
    @100
    simpr
    oveq1d
    wph
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    cB
    @1
    wcel
    wph
    cA
    itgpowd.1
    rexrd
    #
    wph
    cB
    itgpowd.2
    rexrd
    #
    itgpowd.3
    cA
    cB
    ubicc2
    syl3anc
    wph
    cB
    @0
    wph
    cB
    itgpowd.2
    recnd
    @58
    expcld
    fvmptd
    wph
    vt
    cA
    @41
    @6
    @1
    @42
    cc
    @99
    wph
    @30
    cA
    wceq
    #
    wa
    @30
    cA
    @0
    cexp
    wph
    @106
    simpr
    oveq1d
    wph
    @101
    @102
    @103
    cA
    @1
    wcel
    @104
    @105
    itgpowd.3
    cA
    cB
    lbicc2
    syl3anc
    wph
    cA
    @0
    wph
    cA
    itgpowd.1
    recnd
    @58
    expcld
    fvmptd
    oveq12d
    3eqtr3d
    wph
    vx
    cA
    cB
    @27
    itgpowd.1
    itgpowd.2
    @13
    @0
    @3
    wph
    @39
    @12
    @11
    adantr
    @18
    mulcld
    itgioo
    3eqtr3rd
    eqtrd
    mvllmuld
end
