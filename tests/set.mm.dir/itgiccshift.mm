include "caddc.mm"
include "co.mm"
include "cicc.mm"
include "cv.mm"
include "cfv.mm"
include "citg.mm"
include "cdit.mm"
include "c1.mm"
include "cmul.mm"
include "cioo.mm"
include "rpred.mm"
include "leadd1dd.mm"
include "ditgpos.mm"
include "readdcld.mm"
include "cc.mm"
include "cmin.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "ccncf.mm"
include "cncff.mm"
include "syl.mm"
include "adantr.mm"
include "cr.mm"
include "simpr.mm"
include "eliccre.mm"
include "syl3anc.mm"
include "resubcld.mm"
include "cle.mm"
include "wceq.mm"
include "recnd.mm"
include "pncand.mm"
include "eqcomd.mm"
include "wbr.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp2d.mm"
include "lesub1dd.mm"
include "eqbrtrd.mm"
include "simp3d.mm"
include "breqtrd.mm"
include "eliccd.mm"
include "ffvelrnd.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "itgioo.mm"
include "eqtr2d.mm"
include "cmpt.mm"
include "eqid.mm"
include "addccncf.mm"
include "iccssred.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "sselda.mm"
include "cncfmptssg.mm"
include "wrex.mm"
include "crab.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "iccshift.mm"
include "mpteq1d.mm"
include "syl5eq.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "cbvrabv.mm"
include "eqcomi.mm"
include "cncfshift.mm"
include "eqeltrd.mm"
include "feqmptd.mm"
include "oveq1d.mm"
include "3eltr3d.mm"
include "cibl.mm"
include "wss.mm"
include "ioosscn.mm"
include "a1i.mm"
include "1cnd.mm"
include "ssid.mm"
include "constcncfg.mm"
include "csn.mm"
include "cxp.mm"
include "fconstmpt.mm"
include "cvol.mm"
include "cdm.mm"
include "ioombl.mm"
include "ioovolcl.mm"
include "iblconst.mm"
include "syl5eqelr.mm"
include "elind.mm"
include "cdv.mm"
include "crn.mm"
include "ctg.mm"
include "cnt.mm"
include "cres.mm"
include "resmptd.mm"
include "oveq2d.mm"
include "addcld.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "tgioo2.mm"
include "dvres.mm"
include "syl22anc.mm"
include "eqtrd.mm"
include "iccntr.mm"
include "reseq2d.mm"
include "cc0.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "dvmptid.mm"
include "0cnd.mm"
include "dvmptc.mm"
include "dvmptadd.mm"
include "reseq1d.mm"
include "ioossre.mm"
include "1p0e1.mm"
include "mpteq2i.mm"
include "3eqtrd.mm"
include "fveq2.mm"
include "itgsubsticc.mm"
include "mulcld.mm"
include "cbvitgv.mm"
include "cxr.mm"
include "rexrd.mm"
include "iccgelb.mm"
include "iccleub.mm"
include "mulid1d.mm"
include "eqtri.mm"
include "sylan9eqr.mm"
include "fvmptd.mm"
include "itgeq2dv.mm"

theorem itgiccshift
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  let cF: class F
  let cG: class G
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume itgiccshift.a: |- ( ph -> A e. RR )
  assume itgiccshift.b: |- ( ph -> B e. RR )
  assume itgiccshift.aleb: |- ( ph -> A <_ B )
  assume itgiccshift.f: |- ( ph -> F e. ( ( A [,] B ) -cn-> CC ) )
  assume itgiccshift.t: |- ( ph -> T e. RR+ )
  assume itgiccshift.g: |- G = ( x e. ( ( A + T ) [,] ( B + T ) ) |-> ( F ` ( x - T ) ) )

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint G x
  disjoint T x
  disjoint ph x
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint F w
  disjoint G y
  disjoint T w
  disjoint T y
  disjoint T z
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint k x
  assert |- ( ph -> S. ( ( A + T ) [,] ( B + T ) ) ( G ` x ) _d x = S. ( A [,] B ) ( F ` x ) _d x )

  proof
    wph
    vx
    cA
    cT
    caddc
    co
    #
    cB
    cT
    caddc
    co
    #
    cicc
    co
    #
    vx
    cv
    #
    cG
    cfv
    #
    citg
    #
    vx
    @0
    @1
    @4
    cdit
    #
    vy
    cA
    cB
    vy
    cv
    #
    cT
    caddc
    co
    #
    cG
    cfv
    #
    c1
    cmul
    co
    #
    cdit
    #
    vx
    cA
    cB
    cicc
    co
    #
    @3
    cF
    cfv
    #
    citg
    #
    wph
    @6
    vx
    @0
    @1
    cioo
    co
    @4
    citg
    @5
    wph
    vx
    @0
    @1
    @4
    wph
    cA
    cB
    cT
    itgiccshift.a
    itgiccshift.b
    wph
    cT
    itgiccshift.t
    rpred
    #
    itgiccshift.aleb
    leadd1dd
    ditgpos
    wph
    vx
    @0
    @1
    @4
    wph
    cA
    cT
    itgiccshift.a
    @15
    readdcld
    #
    wph
    cB
    cT
    itgiccshift.b
    @15
    readdcld
    #
    wph
    @2
    cc
    @3
    cG
    wph
    vx
    @2
    @3
    cT
    cmin
    co
    #
    cF
    cfv
    #
    cc
    cG
    wph
    @3
    @2
    wcel
    #
    wa
    #
    @12
    cc
    @18
    cF
    wph
    @12
    cc
    cF
    wf
    #
    @20
    wph
    cF
    @12
    cc
    ccncf
    co
    wcel
    @22
    itgiccshift.f
    @12
    cc
    cF
    cncff
    syl
    #
    adantr
    @21
    cA
    cB
    @18
    wph
    cA
    cr
    wcel
    #
    @20
    itgiccshift.a
    adantr
    wph
    cB
    cr
    wcel
    #
    @20
    itgiccshift.b
    adantr
    @21
    @3
    cT
    @21
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @20
    @3
    cr
    wcel
    #
    wph
    @26
    @20
    @16
    adantr
    #
    wph
    @27
    @20
    @17
    adantr
    #
    wph
    @20
    simpr
    #
    @0
    @1
    @3
    eliccre
    syl3anc
    #
    wph
    cT
    cr
    wcel
    #
    @20
    @15
    adantr
    #
    resubcld
    @21
    cA
    @0
    cT
    cmin
    co
    #
    @18
    cle
    wph
    cA
    @35
    wceq
    @20
    wph
    @35
    cA
    wph
    cA
    cT
    wph
    cA
    itgiccshift.a
    recnd
    wph
    cT
    @15
    recnd
    #
    pncand
    eqcomd
    adantr
    @21
    @0
    @3
    cT
    @29
    @32
    @34
    @21
    @28
    @0
    @3
    cle
    wbr
    #
    @3
    @1
    cle
    wbr
    #
    @21
    @20
    @28
    @37
    @38
    w3a
    #
    @31
    @21
    @26
    @27
    @20
    @39
    wb
    @29
    @30
    @0
    @1
    @3
    elicc2
    syl2anc
    mpbid
    #
    simp2d
    lesub1dd
    eqbrtrd
    @21
    @18
    @1
    cT
    cmin
    co
    #
    cB
    cle
    @21
    @3
    @1
    cT
    @32
    @30
    @34
    @21
    @28
    @37
    @38
    @40
    simp3d
    lesub1dd
    wph
    @41
    cB
    wceq
    @20
    wph
    cB
    cT
    wph
    cB
    itgiccshift.b
    recnd
    @36
    pncand
    adantr
    breqtrd
    eliccd
    ffvelrnd
    itgiccshift.g
    fmptd
    #
    ffvelrnda
    itgioo
    eqtr2d
    wph
    vy
    vx
    @8
    c1
    @4
    @9
    @0
    @1
    cA
    cB
    itgiccshift.a
    itgiccshift.b
    itgiccshift.aleb
    wph
    vy
    cc
    cc
    @12
    @2
    @8
    vy
    cc
    @8
    cmpt
    #
    @43
    eqid
    #
    wph
    cT
    cc
    wcel
    #
    @43
    cc
    cc
    ccncf
    co
    wcel
    @36
    vy
    cT
    @43
    @44
    addccncf
    syl
    wph
    @12
    cr
    cc
    wph
    cA
    cB
    itgiccshift.a
    itgiccshift.b
    iccssred
    #
    ax-resscn
    syl6ss
    #
    wph
    @2
    cr
    cc
    wph
    @0
    @1
    @16
    @17
    iccssred
    ax-resscn
    syl6ss
    wph
    @7
    @12
    wcel
    #
    wa
    #
    @0
    @1
    @8
    wph
    @26
    @48
    @16
    adantr
    wph
    @27
    @48
    @17
    adantr
    @49
    @7
    cT
    wph
    @12
    cr
    @7
    @46
    sselda
    #
    wph
    @33
    @48
    @15
    adantr
    #
    readdcld
    @49
    cA
    @7
    cT
    wph
    @24
    @48
    itgiccshift.a
    adantr
    #
    @50
    @51
    @49
    @7
    cr
    wcel
    #
    cA
    @7
    cle
    wbr
    #
    @7
    cB
    cle
    wbr
    #
    @49
    @48
    @53
    @54
    @55
    w3a
    #
    wph
    @48
    simpr
    @49
    @24
    @25
    @48
    @56
    wb
    @52
    wph
    @25
    @48
    itgiccshift.b
    adantr
    #
    cA
    cB
    @7
    elicc2
    syl2anc
    mpbid
    #
    simp2d
    leadd1dd
    @49
    @7
    cB
    cT
    @50
    @57
    @51
    @49
    @53
    @54
    @55
    @58
    simp3d
    leadd1dd
    eliccd
    #
    cncfmptssg
    wph
    cG
    @3
    @8
    wceq
    #
    vy
    @12
    wrex
    #
    vx
    cc
    crab
    #
    cc
    ccncf
    co
    #
    vx
    @2
    @4
    cmpt
    @2
    cc
    ccncf
    co
    wph
    cG
    vw
    @62
    vw
    cv
    #
    cT
    cmin
    co
    #
    cF
    cfv
    #
    cmpt
    #
    @63
    wph
    cG
    vx
    @2
    @19
    cmpt
    #
    @67
    itgiccshift.g
    wph
    @68
    vw
    @2
    @66
    cmpt
    #
    @67
    vx
    vw
    @2
    @19
    @66
    @3
    @64
    wceq
    @18
    @65
    cF
    @3
    @64
    cT
    cmin
    oveq1
    fveq2d
    cbvmptv
    #
    wph
    vw
    @2
    @62
    @66
    wph
    vy
    vx
    cA
    cB
    cT
    itgiccshift.a
    itgiccshift.b
    @15
    iccshift
    #
    mpteq1d
    syl5eq
    syl5eq
    wph
    vw
    vz
    @12
    @62
    cT
    cF
    @67
    @47
    @36
    @64
    vz
    cv
    #
    cT
    caddc
    co
    #
    wceq
    #
    vz
    @12
    wrex
    #
    vw
    cc
    crab
    @62
    @75
    @61
    vw
    vx
    cc
    @64
    @3
    wceq
    #
    @75
    @3
    @73
    wceq
    #
    vz
    @12
    wrex
    @61
    @76
    @74
    @77
    vz
    @12
    @64
    @3
    @73
    eqeq1
    rexbidv
    @77
    @60
    vz
    vy
    @12
    @72
    @7
    wceq
    @73
    @8
    @3
    @72
    @7
    cT
    caddc
    oveq1
    eqeq2d
    cbvrexv
    syl6bb
    cbvrabv
    eqcomi
    itgiccshift.f
    @67
    eqid
    cncfshift
    eqeltrd
    wph
    vx
    @2
    cc
    cG
    @42
    feqmptd
    wph
    @62
    @2
    cc
    ccncf
    wph
    @2
    @62
    @71
    eqcomd
    oveq1d
    3eltr3d
    wph
    cA
    cB
    cioo
    co
    #
    cc
    ccncf
    co
    cibl
    vy
    @78
    c1
    cmpt
    #
    wph
    vy
    @78
    c1
    cc
    @78
    cc
    wss
    wph
    cA
    cB
    ioosscn
    a1i
    wph
    1cnd
    #
    cc
    cc
    wss
    wph
    cc
    ssid
    a1i
    constcncfg
    wph
    @79
    @78
    c1
    csn
    cxp
    #
    cibl
    vy
    @78
    c1
    fconstmpt
    wph
    @78
    cvol
    cdm
    wcel
    #
    @78
    cvol
    cfv
    cr
    wcel
    #
    c1
    cc
    wcel
    @81
    cibl
    wcel
    @82
    wph
    cA
    cB
    ioombl
    a1i
    wph
    @24
    @25
    @83
    itgiccshift.a
    itgiccshift.b
    cA
    cB
    ioovolcl
    syl2anc
    @80
    @78
    c1
    iblconst
    syl3anc
    syl5eqelr
    elind
    wph
    cr
    vy
    @12
    @8
    cmpt
    #
    cdv
    co
    #
    cr
    vy
    cr
    @8
    cmpt
    #
    cdv
    co
    #
    @12
    cioo
    crn
    ctg
    cfv
    #
    cnt
    cfv
    cfv
    #
    cres
    #
    @87
    @78
    cres
    #
    @79
    wph
    @85
    cr
    @86
    @12
    cres
    #
    cdv
    co
    #
    @90
    wph
    @84
    @92
    cr
    cdv
    wph
    @92
    @84
    wph
    vy
    cr
    @12
    @8
    @46
    resmptd
    eqcomd
    oveq2d
    wph
    cr
    cc
    wss
    #
    cr
    cc
    @86
    wf
    cr
    cr
    wss
    #
    @12
    cr
    wss
    @93
    @90
    wceq
    @94
    wph
    ax-resscn
    a1i
    #
    wph
    vy
    cr
    @8
    cc
    @86
    wph
    @53
    wa
    #
    @7
    cT
    wph
    cr
    cc
    @7
    @96
    sselda
    #
    wph
    @45
    @53
    @36
    adantr
    #
    addcld
    @86
    eqid
    fmptd
    @95
    wph
    cr
    ssid
    a1i
    @46
    cr
    @12
    cr
    @88
    @86
    ccnfld
    ctopn
    cfv
    #
    @100
    eqid
    #
    @100
    @101
    tgioo2
    dvres
    syl22anc
    eqtrd
    wph
    @89
    @78
    @87
    wph
    @24
    @25
    @89
    @78
    wceq
    itgiccshift.a
    itgiccshift.b
    cA
    cB
    iccntr
    syl2anc
    reseq2d
    wph
    @91
    vy
    cr
    c1
    cc0
    caddc
    co
    #
    cmpt
    #
    @78
    cres
    vy
    @78
    @102
    cmpt
    #
    @79
    wph
    @87
    @103
    @78
    wph
    vy
    @7
    c1
    cT
    cc0
    cr
    cc
    cc
    cr
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    #
    @98
    @97
    1cnd
    wph
    vy
    cr
    @105
    dvmptid
    @99
    @97
    0cnd
    wph
    vy
    cT
    cr
    @105
    @36
    dvmptc
    dvmptadd
    reseq1d
    wph
    vy
    cr
    @78
    @102
    @78
    cr
    wss
    wph
    cA
    cB
    ioossre
    a1i
    resmptd
    @104
    @79
    wceq
    wph
    vy
    @78
    @102
    c1
    1p0e1
    mpteq2i
    a1i
    3eqtrd
    3eqtrd
    @3
    @8
    cG
    fveq2
    @7
    cA
    cT
    caddc
    oveq1
    @7
    cB
    cT
    caddc
    oveq1
    @16
    @17
    itgsubsticc
    wph
    @11
    vy
    @78
    @10
    citg
    vy
    @12
    @10
    citg
    #
    @14
    wph
    vy
    cA
    cB
    @10
    itgiccshift.aleb
    ditgpos
    wph
    vy
    cA
    cB
    @10
    itgiccshift.a
    itgiccshift.b
    @49
    @9
    c1
    @49
    @2
    cc
    @8
    cG
    wph
    @2
    cc
    cG
    wf
    #
    @48
    @42
    adantr
    @59
    ffvelrnd
    @49
    1cnd
    mulcld
    itgioo
    wph
    @106
    vx
    @12
    @3
    cT
    caddc
    co
    #
    cG
    cfv
    #
    c1
    cmul
    co
    #
    citg
    @14
    vy
    vx
    @12
    @10
    @110
    @7
    @3
    wceq
    #
    @9
    @109
    c1
    cmul
    @111
    @8
    @108
    cG
    @7
    @3
    cT
    caddc
    oveq1
    fveq2d
    oveq1d
    cbvitgv
    wph
    vx
    @12
    @110
    @13
    wph
    @3
    @12
    wcel
    #
    wa
    #
    @110
    @109
    @13
    @113
    @109
    @113
    @2
    cc
    @108
    cG
    wph
    @107
    @112
    @42
    adantr
    @113
    @0
    @1
    @108
    wph
    @26
    @112
    @16
    adantr
    wph
    @27
    @112
    @17
    adantr
    @113
    @3
    cT
    wph
    @12
    cr
    @3
    @46
    sselda
    #
    wph
    @33
    @112
    @15
    adantr
    #
    readdcld
    @113
    cA
    @3
    cT
    wph
    @24
    @112
    itgiccshift.a
    adantr
    @114
    @115
    @113
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @112
    cA
    @3
    cle
    wbr
    wph
    @116
    @112
    wph
    cA
    itgiccshift.a
    rexrd
    adantr
    #
    wph
    @117
    @112
    wph
    cB
    itgiccshift.b
    rexrd
    adantr
    #
    wph
    @112
    simpr
    #
    cA
    cB
    @3
    iccgelb
    syl3anc
    leadd1dd
    @113
    @3
    cB
    cT
    @114
    wph
    @25
    @112
    itgiccshift.b
    adantr
    @115
    @113
    @116
    @117
    @112
    @3
    cB
    cle
    wbr
    @118
    @119
    @120
    cA
    cB
    @3
    iccleub
    syl3anc
    leadd1dd
    eliccd
    #
    ffvelrnd
    mulid1d
    @113
    vw
    @108
    @66
    @13
    @2
    cG
    cc
    cG
    @69
    wceq
    @113
    cG
    @68
    @69
    itgiccshift.g
    @70
    eqtri
    a1i
    @64
    @108
    wceq
    #
    @113
    @66
    @108
    cT
    cmin
    co
    #
    cF
    cfv
    @13
    @122
    @65
    @123
    cF
    @64
    @108
    cT
    cmin
    oveq1
    fveq2d
    @113
    @123
    @3
    cF
    @113
    @3
    cT
    @113
    @3
    @114
    recnd
    wph
    @45
    @112
    @36
    adantr
    pncand
    fveq2d
    sylan9eqr
    @121
    wph
    @12
    cc
    @3
    cF
    @23
    ffvelrnda
    fvmptd
    eqtrd
    itgeq2dv
    syl5eq
    3eqtrd
    3eqtrd
end
