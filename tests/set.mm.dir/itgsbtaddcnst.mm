include "cmin.mm"
include "co.mm"
include "cv.mm"
include "caddc.mm"
include "cfv.mm"
include "cdit.mm"
include "c1.mm"
include "cmul.mm"
include "cicc.mm"
include "cmpt.mm"
include "cneg.mm"
include "ccncf.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "iccssred.mm"
include "sselda.mm"
include "recnd.mm"
include "cc.mm"
include "adantr.mm"
include "negsubd.mm"
include "eqcomd.mm"
include "mpteq2dva.mm"
include "wf.mm"
include "resubcld.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "simpr.mm"
include "wb.mm"
include "jca.mm"
include "elicc2.mm"
include "syl.mm"
include "mpbid.mm"
include "simp2d.mm"
include "lesub1dd.mm"
include "simp3d.mm"
include "eliccd.mm"
include "eqid.mm"
include "fmptd.mm"
include "feq1dd.mm"
include "wss.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "cres.mm"
include "resmptd.mm"
include "ssid.mm"
include "cncfmptid.mm"
include "mp2an.mm"
include "a1i.mm"
include "id.mm"
include "constcncfg.mm"
include "subcncf.mm"
include "rescncf.mm"
include "sylc.mm"
include "eqeltrrd.mm"
include "cncffvrn.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "eqeltrd.mm"
include "addcomd.mm"
include "addccncf.mm"
include "readdcld.mm"
include "lesubadd2d.mm"
include "leaddsub2d.mm"
include "cncfmptssg.mm"
include "cncfcompt.mm"
include "cioo.mm"
include "cibl.mm"
include "ax-1cn.mm"
include "ioosscn.mm"
include "cncfmptc.mm"
include "mp3an.mm"
include "csn.mm"
include "cxp.mm"
include "fconstmpt.mm"
include "cvol.mm"
include "cdm.mm"
include "ioombl.mm"
include "wceq.mm"
include "volioo.mm"
include "syl3anc.mm"
include "1cnd.mm"
include "iblconst.mm"
include "syl5eqelr.mm"
include "elind.mm"
include "cdv.mm"
include "cc0.mm"
include "crn.mm"
include "ctg.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "tgioo2.mm"
include "cnt.mm"
include "iccntr.mm"
include "dvmptntr.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "ioossre.mm"
include "sseli.mm"
include "adantl.mm"
include "dvmptid.mm"
include "iooretop.mm"
include "dvmptres.mm"
include "0cnd.mm"
include "dvmptc.mm"
include "dvmptsub.mm"
include "subid1d.mm"
include "3eqtrd.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq1.mm"
include "itgsubsticc.mm"
include "pncan3d.mm"
include "oveq1d.mm"
include "cncff.mm"
include "ioossicc.mm"
include "ffvelrnd.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "ditgeq3d.mm"

theorem itgsbtaddcnst
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume itgsbtaddcnst.a: |- ( ph -> A e. RR )
  assume itgsbtaddcnst.b: |- ( ph -> B e. RR )
  assume itgsbtaddcnst.aleb: |- ( ph -> A <_ B )
  assume itgsbtaddcnst.x: |- ( ph -> X e. RR )
  assume itgsbtaddcnst.f: |- ( ph -> F e. ( ( A [,] B ) -cn-> CC ) )

  disjoint A s
  disjoint A t
  disjoint s t
  disjoint B s
  disjoint B t
  disjoint F s
  disjoint F t
  disjoint X s
  disjoint X t
  disjoint ph s
  disjoint ph t
  disjoint k x
  assert |- ( ph -> S_ [ ( A - X ) -> ( B - X ) ] ( F ` ( X + s ) ) _d s = S_ [ A -> B ] ( F ` t ) _d t )

  proof
    wph
    vs
    cA
    cX
    cmin
    co
    #
    cB
    cX
    cmin
    co
    #
    cX
    vs
    cv
    #
    caddc
    co
    #
    cF
    cfv
    #
    cdit
    vt
    cA
    cB
    cX
    vt
    cv
    #
    cX
    cmin
    co
    #
    caddc
    co
    #
    cF
    cfv
    #
    c1
    cmul
    co
    #
    cdit
    vt
    cA
    cB
    @5
    cF
    cfv
    #
    cdit
    wph
    vt
    vs
    @6
    c1
    @4
    @8
    @0
    @1
    cA
    cB
    itgsbtaddcnst.a
    itgsbtaddcnst.b
    itgsbtaddcnst.aleb
    wph
    vt
    cA
    cB
    cicc
    co
    #
    @6
    cmpt
    #
    vt
    @11
    @5
    cX
    cneg
    caddc
    co
    #
    cmpt
    #
    @11
    @0
    @1
    cicc
    co
    #
    ccncf
    co
    #
    wph
    vt
    @11
    @6
    @13
    wph
    @5
    @11
    wcel
    #
    wa
    #
    @13
    @6
    @18
    @5
    cX
    @18
    @5
    wph
    @11
    cr
    @5
    wph
    cA
    cB
    itgsbtaddcnst.a
    itgsbtaddcnst.b
    iccssred
    #
    sselda
    #
    recnd
    wph
    cX
    cc
    wcel
    #
    @17
    wph
    cX
    itgsbtaddcnst.x
    recnd
    #
    adantr
    negsubd
    eqcomd
    mpteq2dva
    #
    wph
    @14
    @16
    wcel
    #
    @11
    @15
    @14
    wf
    #
    wph
    @11
    @15
    @12
    @14
    @23
    wph
    vt
    @11
    @6
    @15
    @12
    @18
    @0
    @1
    @6
    @18
    cA
    cX
    wph
    cA
    cr
    wcel
    #
    @17
    itgsbtaddcnst.a
    adantr
    #
    wph
    cX
    cr
    wcel
    #
    @17
    itgsbtaddcnst.x
    adantr
    #
    resubcld
    @18
    cB
    cX
    wph
    cB
    cr
    wcel
    #
    @17
    itgsbtaddcnst.b
    adantr
    #
    @29
    resubcld
    @18
    @5
    cX
    @20
    @29
    resubcld
    #
    @18
    cA
    @5
    cX
    @27
    @20
    @29
    @18
    @5
    cr
    wcel
    #
    cA
    @5
    cle
    wbr
    #
    @5
    cB
    cle
    wbr
    #
    @18
    @17
    @33
    @34
    @35
    w3a
    #
    wph
    @17
    simpr
    @18
    @26
    @30
    wa
    #
    @17
    @36
    wb
    wph
    @37
    @17
    wph
    @26
    @30
    itgsbtaddcnst.a
    itgsbtaddcnst.b
    jca
    #
    adantr
    cA
    cB
    @5
    elicc2
    syl
    mpbid
    #
    simp2d
    lesub1dd
    @18
    @5
    cB
    cX
    @20
    @31
    @29
    @18
    @33
    @34
    @35
    @39
    simp3d
    lesub1dd
    eliccd
    @12
    eqid
    fmptd
    feq1dd
    wph
    @15
    cc
    wss
    @14
    @11
    cc
    ccncf
    co
    #
    wcel
    @24
    @25
    wb
    wph
    @15
    cr
    cc
    wph
    @0
    @1
    wph
    cA
    cX
    itgsbtaddcnst.a
    itgsbtaddcnst.x
    resubcld
    #
    wph
    cB
    cX
    itgsbtaddcnst.b
    itgsbtaddcnst.x
    resubcld
    #
    iccssred
    #
    ax-resscn
    syl6ss
    #
    wph
    @12
    @14
    @40
    @23
    wph
    vt
    cc
    @6
    cmpt
    #
    @11
    cres
    #
    @12
    @40
    wph
    vt
    cc
    @11
    @6
    wph
    @11
    cr
    cc
    @19
    ax-resscn
    syl6ss
    #
    resmptd
    wph
    @11
    cc
    wss
    @45
    cc
    cc
    ccncf
    co
    #
    wcel
    #
    @46
    @40
    wcel
    @47
    wph
    @21
    @49
    @22
    @21
    vt
    @5
    cX
    cc
    vt
    cc
    @5
    cmpt
    @48
    wcel
    #
    @21
    cc
    cc
    wss
    #
    @51
    @50
    cc
    ssid
    #
    @52
    vt
    cc
    cc
    cncfmptid
    mp2an
    a1i
    @21
    vt
    cc
    cX
    cc
    @51
    @21
    @52
    a1i
    #
    @21
    id
    @53
    constcncfg
    subcncf
    syl
    cc
    cc
    @11
    @45
    rescncf
    sylc
    eqeltrrd
    eqeltrrd
    @11
    cc
    @15
    @14
    cncffvrn
    syl2anc
    mpbird
    eqeltrd
    wph
    vs
    @15
    @3
    @11
    cc
    cF
    wph
    vs
    cc
    cc
    @15
    @11
    @3
    vs
    cc
    @3
    cmpt
    #
    @54
    eqid
    wph
    @54
    vs
    cc
    @2
    cX
    caddc
    co
    #
    cmpt
    #
    @48
    wph
    vs
    cc
    @3
    @55
    wph
    @2
    cc
    wcel
    #
    wa
    cX
    @2
    wph
    @21
    @57
    @22
    adantr
    wph
    @57
    simpr
    addcomd
    mpteq2dva
    wph
    @21
    @56
    @48
    wcel
    @22
    vs
    cX
    @56
    @56
    eqid
    addccncf
    syl
    eqeltrd
    @44
    @47
    wph
    @2
    @15
    wcel
    #
    wa
    #
    cA
    cB
    @3
    wph
    @26
    @58
    itgsbtaddcnst.a
    adantr
    #
    wph
    @30
    @58
    itgsbtaddcnst.b
    adantr
    #
    @59
    cX
    @2
    wph
    @28
    @58
    itgsbtaddcnst.x
    adantr
    #
    wph
    @15
    cr
    @2
    @43
    sselda
    #
    readdcld
    @59
    @0
    @2
    cle
    wbr
    #
    cA
    @3
    cle
    wbr
    @59
    @2
    cr
    wcel
    #
    @64
    @2
    @1
    cle
    wbr
    #
    @59
    @58
    @65
    @64
    @66
    w3a
    #
    wph
    @58
    simpr
    @59
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @58
    @67
    wb
    wph
    @68
    @58
    @41
    adantr
    wph
    @69
    @58
    @42
    adantr
    @0
    @1
    @2
    elicc2
    syl2anc
    mpbid
    #
    simp2d
    @59
    cA
    cX
    @2
    @60
    @62
    @63
    lesubadd2d
    mpbid
    @59
    @3
    cB
    cle
    wbr
    @66
    @59
    @65
    @64
    @66
    @70
    simp3d
    @59
    cX
    @2
    cB
    @62
    @63
    @61
    leaddsub2d
    mpbird
    eliccd
    cncfmptssg
    itgsbtaddcnst.f
    cncfcompt
    wph
    cA
    cB
    cioo
    co
    #
    cc
    ccncf
    co
    #
    cibl
    vt
    @71
    c1
    cmpt
    #
    @73
    @72
    wcel
    #
    wph
    c1
    cc
    wcel
    #
    @71
    cc
    wss
    @51
    @74
    ax-1cn
    cA
    cB
    ioosscn
    @52
    vt
    c1
    @71
    cc
    cncfmptc
    mp3an
    a1i
    wph
    @73
    @71
    c1
    csn
    cxp
    #
    cibl
    vt
    @71
    c1
    fconstmpt
    wph
    @71
    cvol
    cdm
    wcel
    #
    @71
    cvol
    cfv
    #
    cr
    wcel
    @75
    @76
    cibl
    wcel
    @77
    wph
    cA
    cB
    ioombl
    a1i
    wph
    @78
    cB
    cA
    cmin
    co
    #
    cr
    wph
    @26
    @30
    cA
    cB
    cle
    wbr
    @78
    @79
    wceq
    itgsbtaddcnst.a
    itgsbtaddcnst.b
    itgsbtaddcnst.aleb
    cA
    cB
    volioo
    syl3anc
    wph
    cB
    cA
    itgsbtaddcnst.b
    itgsbtaddcnst.a
    resubcld
    eqeltrd
    wph
    1cnd
    @71
    c1
    iblconst
    syl3anc
    syl5eqelr
    elind
    wph
    cr
    @12
    cdv
    co
    cr
    vt
    @71
    @6
    cmpt
    cdv
    co
    vt
    @71
    c1
    cc0
    cmin
    co
    #
    cmpt
    @73
    wph
    vt
    @6
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
    @11
    @71
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    #
    @19
    @18
    @6
    @32
    recnd
    @82
    @82
    eqid
    #
    tgioo2
    #
    @84
    wph
    @37
    @11
    @81
    cnt
    cfv
    cfv
    @71
    wceq
    @38
    cA
    cB
    iccntr
    syl
    dvmptntr
    wph
    vt
    @5
    c1
    cX
    cc0
    cr
    cc
    cc
    @71
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    #
    wph
    @5
    @71
    wcel
    #
    wa
    #
    @5
    @87
    @33
    wph
    @71
    cr
    @5
    cA
    cB
    ioossre
    #
    sseli
    adantl
    recnd
    #
    @88
    1cnd
    #
    wph
    vt
    @5
    c1
    cr
    @81
    @82
    cc
    cr
    @71
    @86
    wph
    cr
    cc
    @5
    @83
    sselda
    wph
    @33
    wa
    #
    1cnd
    wph
    vt
    cr
    @86
    dvmptid
    @71
    cr
    wss
    wph
    @89
    a1i
    #
    @85
    @84
    @71
    @81
    wcel
    wph
    cA
    cB
    iooretop
    a1i
    #
    dvmptres
    wph
    @21
    @87
    @22
    adantr
    #
    @88
    0cnd
    wph
    vt
    cX
    cc0
    cr
    @81
    @82
    cc
    cr
    @71
    @86
    wph
    @21
    @33
    @22
    adantr
    @92
    0cnd
    wph
    vt
    cX
    cr
    @86
    @22
    dvmptc
    @93
    @85
    @84
    @94
    dvmptres
    dvmptsub
    wph
    vt
    @71
    @80
    c1
    @88
    c1
    @91
    subid1d
    mpteq2dva
    3eqtrd
    @2
    @6
    wceq
    @3
    @7
    cF
    @2
    @6
    cX
    caddc
    oveq2
    fveq2d
    @5
    cA
    cX
    cmin
    oveq1
    @5
    cB
    cX
    cmin
    oveq1
    @41
    @42
    itgsubsticc
    wph
    vt
    cA
    cB
    @9
    @10
    itgsbtaddcnst.aleb
    @88
    @9
    @10
    c1
    cmul
    co
    @10
    @88
    @8
    @10
    c1
    cmul
    @88
    @7
    @5
    cF
    @88
    cX
    @5
    @95
    @90
    pncan3d
    fveq2d
    oveq1d
    @88
    @10
    @88
    @11
    cc
    @5
    cF
    wph
    @11
    cc
    cF
    wf
    #
    @87
    wph
    cF
    @40
    wcel
    @96
    itgsbtaddcnst.f
    @11
    cc
    cF
    cncff
    syl
    adantr
    @87
    @17
    wph
    @71
    @11
    @5
    cA
    cB
    ioossicc
    sseli
    adantl
    ffvelrnd
    mulid1d
    eqtrd
    ditgeq3d
    eqtrd
end
