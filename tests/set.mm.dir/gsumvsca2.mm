include "cfn.mm"
include "wcel.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "wss.mm"
include "ssid.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "sseq1.mm"
include "anbi2d.mm"
include "mpteq1.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "c0g.mm"
include "cfv.mm"
include "cslmd.mm"
include "eqid.mm"
include "slmd0vs.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "mpt0.mm"
include "oveq2i.mm"
include "gsum0.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "3eqtr4g.mm"
include "adantr.mm"
include "wel.mm"
include "wn.mm"
include "ssun1.mm"
include "sstr2.mm"
include "ax-mp.mm"
include "anim2i.mm"
include "imim1i.mm"
include "csb.mm"
include "cplusg.mm"
include "cbs.mm"
include "ad2antrl.mm"
include "cvv.mm"
include "csrg.mm"
include "ccmn.mm"
include "slmdsrg.mm"
include "srgcmn.mm"
include "3syl.mm"
include "vex.mm"
include "a1i.mm"
include "simplrl.mm"
include "simprr.mm"
include "unssad.mm"
include "sselda.mm"
include "sseldd.mm"
include "fmptd.mm"
include "simpll.mm"
include "fvexd.mm"
include "fsuppmptdm.mm"
include "gsumcl.mm"
include "wral.mm"
include "unssbd.mm"
include "snss.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "rspcsbela.mm"
include "slmdvsdir.mm"
include "syl13anc.mm"
include "nfcsb1v.mm"
include "simplr.mm"
include "csbeq1a.mm"
include "gsumunsnf.mm"
include "nfcv.mm"
include "nfov.mm"
include "slmdcmn.mm"
include "syl.mm"
include "slmdvscl.mm"
include "syl3anc.mm"
include "simpr.mm"
include "eqtrd.mm"
include "3eqtr4rd.mm"
include "exp31.mm"
include "a2d.mm"
include "syl5.mm"
include "findcard2s.mm"
include "imp.mm"
include "mpanr2.mm"
include "mpancom.mm"

theorem gsumvsca2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let c.pl: class .+
  let cQ: class Q
  let c.x: class .x.
  let vk: setvar k
  let cG: class G
  let cK: class K
  let cW: class W
  let c.0: class .0.
  let va: setvar a
  let ve: setvar e
  let vz: setvar z
  assume gsumvsca.b: |- B = ( Base ` W )
  assume gsumvsca.g: |- G = ( Scalar ` W )
  assume gsumvsca.z: |- .0. = ( 0g ` W )
  assume gsumvsca.t: |- .x. = ( .s ` W )
  assume gsumvsca.p: |- .+ = ( +g ` W )
  assume gsumvsca.k: |- ( ph -> K C_ ( Base ` G ) )
  assume gsumvsca.a: |- ( ph -> A e. Fin )
  assume gsumvsca.w: |- ( ph -> W e. SLMod )
  assume gsumvsca2.n: |- ( ph -> Q e. B )
  assume gsumvsca2.c: |- ( ( ph /\ k e. A ) -> P e. K )

  disjoint G k
  disjoint K k
  disjoint Q k
  disjoint .x. k
  disjoint A k
  disjoint W k
  disjoint k ph
  disjoint B k
  disjoint a e
  disjoint a k
  disjoint a z
  disjoint G a
  disjoint e k
  disjoint e z
  disjoint G e
  disjoint k z
  disjoint G z
  disjoint a e
  disjoint a k
  disjoint a z
  disjoint .x. a
  disjoint e k
  disjoint e z
  disjoint .x. e
  disjoint k z
  disjoint .x. z
  disjoint A a
  disjoint A e
  disjoint A z
  disjoint P a
  disjoint P e
  disjoint P z
  disjoint Q a
  disjoint Q e
  disjoint Q z
  disjoint W a
  disjoint W e
  disjoint W z
  disjoint a ph
  disjoint e ph
  disjoint ph z
  assert |- ( ph -> ( W gsum ( k e. A |-> ( P .x. Q ) ) ) = ( ( G gsum ( k e. A |-> P ) ) .x. Q ) )

  proof
    cA
    cfn
    wcel
    #
    wph
    cW
    vk
    cA
    cP
    cQ
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cG
    vk
    cA
    cP
    cmpt
    #
    cgsu
    co
    #
    cQ
    c.x
    co
    #
    wceq
    #
    gsumvsca.a
    @0
    wph
    cA
    cA
    wss
    #
    @7
    cA
    ssid
    @0
    wph
    @8
    wa
    #
    @7
    wph
    va
    cv
    #
    cA
    wss
    #
    wa
    #
    cW
    vk
    @10
    @1
    cmpt
    #
    cgsu
    co
    #
    cG
    vk
    @10
    cP
    cmpt
    #
    cgsu
    co
    #
    cQ
    c.x
    co
    #
    wceq
    #
    wi
    wph
    c0
    cA
    wss
    #
    wa
    #
    cW
    vk
    c0
    @1
    cmpt
    #
    cgsu
    co
    #
    cG
    vk
    c0
    cP
    cmpt
    #
    cgsu
    co
    #
    cQ
    c.x
    co
    #
    wceq
    #
    wi
    wph
    ve
    cv
    #
    cA
    wss
    #
    wa
    #
    cW
    vk
    @27
    @1
    cmpt
    #
    cgsu
    co
    #
    cG
    vk
    @27
    cP
    cmpt
    #
    cgsu
    co
    #
    cQ
    c.x
    co
    #
    wceq
    #
    wi
    #
    wph
    @27
    vz
    cv
    #
    csn
    #
    cun
    #
    cA
    wss
    #
    wa
    #
    cW
    vk
    @39
    @1
    cmpt
    #
    cgsu
    co
    #
    cG
    vk
    @39
    cP
    cmpt
    #
    cgsu
    co
    #
    cQ
    c.x
    co
    #
    wceq
    #
    wi
    #
    @9
    @7
    wi
    va
    ve
    vz
    cA
    @10
    c0
    wceq
    #
    @12
    @20
    @18
    @26
    @49
    @11
    @19
    wph
    @10
    c0
    cA
    sseq1
    anbi2d
    @49
    @14
    @22
    @17
    @25
    @49
    @13
    @21
    cW
    cgsu
    vk
    @10
    c0
    @1
    mpteq1
    oveq2d
    @49
    @16
    @24
    cQ
    c.x
    @49
    @15
    @23
    cG
    cgsu
    vk
    @10
    c0
    cP
    mpteq1
    oveq2d
    oveq1d
    eqeq12d
    imbi12d
    @10
    @27
    wceq
    #
    @12
    @29
    @18
    @35
    @50
    @11
    @28
    wph
    @10
    @27
    cA
    sseq1
    anbi2d
    @50
    @14
    @31
    @17
    @34
    @50
    @13
    @30
    cW
    cgsu
    vk
    @10
    @27
    @1
    mpteq1
    oveq2d
    @50
    @16
    @33
    cQ
    c.x
    @50
    @15
    @32
    cG
    cgsu
    vk
    @10
    @27
    cP
    mpteq1
    oveq2d
    oveq1d
    eqeq12d
    imbi12d
    @10
    @39
    wceq
    #
    @12
    @41
    @18
    @47
    @51
    @11
    @40
    wph
    @10
    @39
    cA
    sseq1
    anbi2d
    @51
    @14
    @43
    @17
    @46
    @51
    @13
    @42
    cW
    cgsu
    vk
    @10
    @39
    @1
    mpteq1
    oveq2d
    @51
    @16
    @45
    cQ
    c.x
    @51
    @15
    @44
    cG
    cgsu
    vk
    @10
    @39
    cP
    mpteq1
    oveq2d
    oveq1d
    eqeq12d
    imbi12d
    @10
    cA
    wceq
    #
    @12
    @9
    @18
    @7
    @52
    @11
    @8
    wph
    @10
    cA
    cA
    sseq1
    anbi2d
    @52
    @14
    @3
    @17
    @6
    @52
    @13
    @2
    cW
    cgsu
    vk
    @10
    cA
    @1
    mpteq1
    oveq2d
    @52
    @16
    @5
    cQ
    c.x
    @52
    @15
    @4
    cG
    cgsu
    vk
    @10
    cA
    cP
    mpteq1
    oveq2d
    oveq1d
    eqeq12d
    imbi12d
    wph
    @26
    @19
    wph
    c.0
    cG
    c0g
    cfv
    #
    cQ
    c.x
    co
    #
    @22
    @25
    wph
    @54
    c.0
    wph
    cW
    cslmd
    wcel
    #
    cQ
    cB
    wcel
    #
    @54
    c.0
    wceq
    gsumvsca.w
    gsumvsca2.n
    c.x
    cG
    @53
    cB
    cW
    cQ
    c.0
    gsumvsca.b
    gsumvsca.g
    gsumvsca.t
    @53
    eqid
    #
    gsumvsca.z
    slmd0vs
    syl2anc
    eqcomd
    @22
    cW
    c0
    cgsu
    co
    c.0
    @21
    c0
    cW
    cgsu
    vk
    @1
    mpt0
    oveq2i
    cW
    c.0
    gsumvsca.z
    gsum0
    eqtri
    @24
    @53
    cQ
    c.x
    @24
    cG
    c0
    cgsu
    co
    @53
    @23
    c0
    cG
    cgsu
    vk
    cP
    mpt0
    oveq2i
    cG
    @53
    @57
    gsum0
    eqtri
    oveq1i
    3eqtr4g
    adantr
    @36
    @41
    @35
    wi
    @27
    cfn
    wcel
    #
    vz
    ve
    wel
    wn
    #
    wa
    #
    @48
    @41
    @29
    @35
    @40
    @28
    wph
    @27
    @39
    wss
    @40
    @28
    wi
    @27
    @38
    ssun1
    @27
    @39
    cA
    sstr2
    ax-mp
    anim2i
    imim1i
    @60
    @41
    @35
    @47
    @60
    @41
    @35
    @47
    @60
    @41
    wa
    #
    @35
    wa
    #
    @33
    vk
    @37
    cP
    csb
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cQ
    c.x
    co
    #
    @34
    @63
    cQ
    c.x
    co
    #
    c.pl
    co
    #
    @46
    @43
    @61
    @66
    @68
    wceq
    #
    @35
    @61
    @55
    @33
    cG
    cbs
    cfv
    #
    wcel
    @63
    @70
    wcel
    #
    @56
    @69
    wph
    @55
    @60
    @40
    gsumvsca.w
    ad2antrl
    #
    @61
    @27
    @70
    @32
    cG
    cvv
    @53
    @70
    eqid
    #
    @57
    @61
    @55
    cG
    csrg
    wcel
    cG
    ccmn
    wcel
    @72
    cG
    cW
    gsumvsca.g
    slmdsrg
    cG
    srgcmn
    3syl
    #
    @27
    cvv
    wcel
    @61
    ve
    vex
    a1i
    @61
    vk
    @27
    cP
    @70
    @32
    @61
    vk
    ve
    wel
    #
    wa
    #
    wph
    vk
    cv
    #
    cA
    wcel
    #
    cP
    @70
    wcel
    #
    @60
    wph
    @40
    @75
    simplrl
    #
    @61
    @27
    cA
    @77
    @61
    @27
    @38
    cA
    @60
    wph
    @40
    simprr
    #
    unssad
    sselda
    #
    wph
    @78
    wa
    cK
    @70
    cP
    wph
    cK
    @70
    wss
    @78
    gsumvsca.k
    adantr
    gsumvsca2.c
    sseldd
    #
    syl2anc
    #
    @32
    eqid
    #
    fmptd
    @61
    vk
    @27
    @32
    cK
    cvv
    cP
    @53
    @85
    @58
    @59
    @41
    simpll
    #
    @76
    wph
    @78
    cP
    cK
    wcel
    @80
    @82
    gsumvsca2.c
    syl2anc
    @61
    cG
    c0g
    fvexd
    fsuppmptdm
    gsumcl
    @61
    @37
    cA
    wcel
    #
    @79
    vk
    cA
    wral
    #
    @71
    @61
    @38
    cA
    wss
    @87
    @61
    @27
    @38
    cA
    @81
    unssbd
    @37
    cA
    vz
    vex
    #
    snss
    sylibr
    wph
    @88
    @60
    @40
    wph
    @79
    vk
    cA
    @83
    ralrimiva
    ad2antrl
    vk
    @37
    cA
    cP
    @70
    rspcsbela
    syl2anc
    #
    wph
    @56
    @60
    @40
    gsumvsca2.n
    ad2antrl
    #
    c.pl
    @64
    @33
    @63
    c.x
    cG
    @70
    cB
    cW
    cQ
    gsumvsca.b
    gsumvsca.p
    gsumvsca.g
    gsumvsca.t
    @73
    @64
    eqid
    #
    slmdvsdir
    syl13anc
    adantr
    @61
    @46
    @66
    wceq
    @35
    @61
    @45
    @65
    cQ
    c.x
    @61
    @27
    @70
    @64
    vk
    cG
    @37
    cvv
    cP
    @63
    vk
    @37
    cP
    nfcsb1v
    #
    @73
    @92
    @74
    @86
    @84
    @37
    cvv
    wcel
    @61
    @89
    a1i
    #
    @58
    @59
    @41
    simplr
    #
    @90
    vk
    @37
    cP
    csbeq1a
    #
    gsumunsnf
    oveq1d
    adantr
    @62
    @43
    @31
    @67
    c.pl
    co
    #
    @68
    @61
    @43
    @97
    wceq
    @35
    @61
    @27
    cB
    c.pl
    vk
    cW
    @37
    cvv
    @1
    @67
    vk
    @63
    cQ
    c.x
    @93
    vk
    c.x
    nfcv
    vk
    cQ
    nfcv
    nfov
    gsumvsca.b
    gsumvsca.p
    @61
    @55
    cW
    ccmn
    wcel
    @72
    cW
    slmdcmn
    syl
    @86
    @76
    @55
    @79
    @56
    @1
    cB
    wcel
    @76
    wph
    @55
    @80
    gsumvsca.w
    syl
    @84
    @76
    wph
    @56
    @80
    gsumvsca2.n
    syl
    cP
    c.x
    cG
    @70
    cB
    cW
    cQ
    gsumvsca.b
    gsumvsca.g
    gsumvsca.t
    @73
    slmdvscl
    syl3anc
    @94
    @95
    @61
    @55
    @71
    @56
    @67
    cB
    wcel
    @72
    @90
    @91
    @63
    c.x
    cG
    @70
    cB
    cW
    cQ
    gsumvsca.b
    gsumvsca.g
    gsumvsca.t
    @73
    slmdvscl
    syl3anc
    @77
    @37
    wceq
    cP
    @63
    cQ
    c.x
    @96
    oveq1d
    gsumunsnf
    adantr
    @62
    @31
    @34
    @67
    c.pl
    @61
    @35
    simpr
    oveq1d
    eqtrd
    3eqtr4rd
    exp31
    a2d
    syl5
    findcard2s
    imp
    mpanr2
    mpancom
end
