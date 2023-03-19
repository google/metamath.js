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
include "eqeq12d.mm"
include "imbi12d.mm"
include "cslmd.mm"
include "cbs.mm"
include "cfv.mm"
include "sseldd.mm"
include "eqid.mm"
include "slmdvs0.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "mpt0.mm"
include "oveq2i.mm"
include "gsum0.mm"
include "eqtri.mm"
include "3eqtr4g.mm"
include "adantr.mm"
include "wn.mm"
include "ssun1.mm"
include "sstr2.mm"
include "ax-mp.mm"
include "anim2i.mm"
include "imim1i.mm"
include "csb.mm"
include "ad2antrl.mm"
include "cvv.mm"
include "ccmn.mm"
include "slmdcmn.mm"
include "syl.mm"
include "vex.mm"
include "a1i.mm"
include "simplrl.mm"
include "simprr.mm"
include "unssad.mm"
include "sselda.mm"
include "fmptd.mm"
include "simpll.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fsuppmptdm.mm"
include "gsumcl.mm"
include "wral.mm"
include "unssbd.mm"
include "snss.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "rspcsbela.mm"
include "slmdvsdi.mm"
include "syl13anc.mm"
include "nfcsb1v.mm"
include "simplr.mm"
include "csbeq1a.mm"
include "gsumunsnf.mm"
include "nfcv.mm"
include "nfov.mm"
include "slmdvscl.mm"
include "syl3anc.mm"
include "simpr.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "3eqtr4rd.mm"
include "exp31.mm"
include "a2d.mm"
include "syl5.mm"
include "findcard2s.mm"
include "imp.mm"
include "mpanr2.mm"
include "mpancom.mm"

theorem gsumvsca1
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
  assume gsumvsca1.n: |- ( ph -> P e. K )
  assume gsumvsca1.c: |- ( ( ph /\ k e. A ) -> Q e. B )

  disjoint P k
  disjoint .x. k
  disjoint A k
  disjoint W k
  disjoint k ph
  disjoint B k
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
  assert |- ( ph -> ( W gsum ( k e. A |-> ( P .x. Q ) ) ) = ( P .x. ( W gsum ( k e. A |-> Q ) ) ) )

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
    cP
    cW
    vk
    cA
    cQ
    cmpt
    #
    cgsu
    co
    #
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
    cP
    cW
    vk
    @10
    cQ
    cmpt
    #
    cgsu
    co
    #
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
    cP
    cW
    vk
    c0
    cQ
    cmpt
    #
    cgsu
    co
    #
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
    cP
    cW
    vk
    @27
    cQ
    cmpt
    #
    cgsu
    co
    #
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
    cP
    cW
    vk
    @39
    cQ
    cmpt
    #
    cgsu
    co
    #
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
    cP
    c.x
    @49
    @15
    @23
    cW
    cgsu
    vk
    @10
    c0
    cQ
    mpteq1
    oveq2d
    oveq2d
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
    cP
    c.x
    @50
    @15
    @32
    cW
    cgsu
    vk
    @10
    @27
    cQ
    mpteq1
    oveq2d
    oveq2d
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
    cP
    c.x
    @51
    @15
    @44
    cW
    cgsu
    vk
    @10
    @39
    cQ
    mpteq1
    oveq2d
    oveq2d
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
    cP
    c.x
    @52
    @15
    @4
    cW
    cgsu
    vk
    @10
    cA
    cQ
    mpteq1
    oveq2d
    oveq2d
    eqeq12d
    imbi12d
    wph
    @26
    @19
    wph
    c.0
    cP
    c.0
    c.x
    co
    #
    @22
    @25
    wph
    @53
    c.0
    wph
    cW
    cslmd
    wcel
    #
    cP
    cG
    cbs
    cfv
    #
    wcel
    #
    @53
    c.0
    wceq
    gsumvsca.w
    wph
    cK
    @55
    cP
    gsumvsca.k
    gsumvsca1.n
    sseldd
    #
    c.x
    cG
    @55
    cW
    cP
    c.0
    gsumvsca.g
    gsumvsca.t
    @55
    eqid
    #
    gsumvsca.z
    slmdvs0
    syl2anc
    eqcomd
    @22
    cW
    c0
    cgsu
    co
    #
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
    #
    eqtri
    @24
    c.0
    cP
    c.x
    @24
    @59
    c.0
    @23
    c0
    cW
    cgsu
    vk
    cQ
    mpt0
    oveq2i
    @60
    eqtri
    oveq2i
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
    @37
    @27
    wcel
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
    @63
    @41
    @35
    @47
    @63
    @41
    @35
    @47
    @63
    @41
    wa
    #
    @35
    wa
    #
    cP
    @33
    vk
    @37
    cQ
    csb
    #
    c.pl
    co
    #
    c.x
    co
    #
    @34
    cP
    @66
    c.x
    co
    #
    c.pl
    co
    #
    @46
    @43
    @64
    @68
    @70
    wceq
    #
    @35
    @64
    @54
    @56
    @33
    cB
    wcel
    @66
    cB
    wcel
    #
    @71
    wph
    @54
    @63
    @40
    gsumvsca.w
    ad2antrl
    #
    wph
    @56
    @63
    @40
    @57
    ad2antrl
    #
    @64
    @27
    cB
    @32
    cW
    cvv
    c.0
    gsumvsca.b
    gsumvsca.z
    @64
    @54
    cW
    ccmn
    wcel
    @73
    cW
    slmdcmn
    syl
    #
    @27
    cvv
    wcel
    @64
    ve
    vex
    a1i
    @64
    vk
    @27
    cQ
    cB
    @32
    @64
    vk
    cv
    #
    @27
    wcel
    #
    wa
    #
    wph
    @76
    cA
    wcel
    cQ
    cB
    wcel
    #
    @63
    wph
    @40
    @77
    simplrl
    #
    @64
    @27
    cA
    @76
    @64
    @27
    @38
    cA
    @63
    wph
    @40
    simprr
    #
    unssad
    sselda
    gsumvsca1.c
    syl2anc
    #
    @32
    eqid
    #
    fmptd
    @64
    vk
    @27
    @32
    cB
    cvv
    cQ
    c.0
    @83
    @61
    @62
    @41
    simpll
    #
    @82
    c.0
    cvv
    wcel
    @64
    c.0
    cW
    c0g
    cfv
    cvv
    gsumvsca.z
    cW
    c0g
    fvex
    eqeltri
    a1i
    fsuppmptdm
    gsumcl
    @64
    @37
    cA
    wcel
    #
    @79
    vk
    cA
    wral
    #
    @72
    @64
    @38
    cA
    wss
    @85
    @64
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
    @86
    @63
    @40
    wph
    @79
    vk
    cA
    gsumvsca1.c
    ralrimiva
    ad2antrl
    vk
    @37
    cA
    cQ
    cB
    rspcsbela
    syl2anc
    #
    c.pl
    cP
    c.x
    cG
    @55
    cB
    cW
    @33
    @66
    gsumvsca.b
    gsumvsca.p
    gsumvsca.g
    gsumvsca.t
    @58
    slmdvsdi
    syl13anc
    adantr
    @64
    @46
    @68
    wceq
    @35
    @64
    @45
    @67
    cP
    c.x
    @64
    @27
    cB
    c.pl
    vk
    cW
    @37
    cvv
    cQ
    @66
    vk
    @37
    cQ
    nfcsb1v
    #
    gsumvsca.b
    gsumvsca.p
    @75
    @84
    @82
    @37
    cvv
    wcel
    @64
    @87
    a1i
    #
    @61
    @62
    @41
    simplr
    #
    @88
    vk
    @37
    cQ
    csbeq1a
    #
    gsumunsnf
    oveq2d
    adantr
    @65
    @43
    @31
    @69
    c.pl
    co
    #
    @70
    @64
    @43
    @93
    wceq
    @35
    @64
    @27
    cB
    c.pl
    vk
    cW
    @37
    cvv
    @1
    @69
    vk
    cP
    @66
    c.x
    vk
    cP
    nfcv
    vk
    c.x
    nfcv
    @89
    nfov
    gsumvsca.b
    gsumvsca.p
    @75
    @84
    @78
    @54
    @56
    @79
    @1
    cB
    wcel
    @78
    wph
    @54
    @80
    gsumvsca.w
    syl
    @78
    wph
    @56
    @80
    @57
    syl
    @82
    cP
    c.x
    cG
    @55
    cB
    cW
    cQ
    gsumvsca.b
    gsumvsca.g
    gsumvsca.t
    @58
    slmdvscl
    syl3anc
    @90
    @91
    @64
    @54
    @56
    @72
    @69
    cB
    wcel
    @73
    @74
    @88
    cP
    c.x
    cG
    @55
    cB
    cW
    @66
    gsumvsca.b
    gsumvsca.g
    gsumvsca.t
    @58
    slmdvscl
    syl3anc
    @76
    @37
    wceq
    cQ
    @66
    cP
    c.x
    @92
    oveq2d
    gsumunsnf
    adantr
    @65
    @31
    @34
    @69
    c.pl
    @64
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
