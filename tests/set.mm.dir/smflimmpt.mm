include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "cuz.mm"
include "ciin.mm"
include "ciun.mm"
include "crab.mm"
include "csmblfn.mm"
include "wceq.mm"
include "a1i.mm"
include "wa.mm"
include "nfv.mm"
include "nfan.mm"
include "cvv.mm"
include "uztrn2.mm"
include "adantll.mm"
include "simpll.mm"
include "mptexd.mm"
include "syl2anc.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "dmeqd.mm"
include "simplll.mm"
include "adantr.mm"
include "simpr.mm"
include "syl3anc.mm"
include "fnmptd.mm"
include "fndmd.mm"
include "eqtr2d.mm"
include "iineq2d.mm"
include "iuneq2df.mm"
include "eqcomd.mm"
include "eqtr4d.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "adantrr.mm"
include "wrex.mm"
include "eliun.mm"
include "biimpi.mm"
include "adantl.mm"
include "wi.mm"
include "simpllr.mm"
include "wb.mm"
include "nfcv.mm"
include "nfii1.mm"
include "nfel.mm"
include "cz.mm"
include "eluzelz2.mm"
include "ad2antlr.mm"
include "fvexi.mm"
include "wss.mm"
include "uzssd3.mm"
include "fvexd.mm"
include "eliinid.mm"
include "adantlr.mm"
include "climeldmeqmpt3.mm"
include "adantllr.mm"
include "mpbird.mm"
include "exp31.mm"
include "rexlimd.mm"
include "adantrl.mm"
include "mpd.mm"
include "jca.mm"
include "ex.mm"
include "biimpar.mm"
include "syl.mm"
include "mpbid.mm"
include "impbid.mm"
include "rabbida3.mm"
include "eqtrd.mm"
include "eleq2i.mm"
include "rabidim1.mm"
include "3syl.mm"
include "nfiu1.mm"
include "nfrab.mm"
include "nfcxfr.mm"
include "w3a.mm"
include "nf3an.mm"
include "simp2.mm"
include "uzssd2.mm"
include "3ad2antl3.mm"
include "simpl1.mm"
include "sylan.mm"
include "climfveqmpt3.mm"
include "3exp.mm"
include "mpteq12da.mm"
include "fveq1d.mm"
include "mpteq2da.mm"
include "eleq1d.mm"
include "rabbida2.mm"
include "fveq2d.mm"
include "mpteq12d.mm"
include "3eqtrd.mm"
include "nfmpt1.mm"
include "nfmpt.mm"
include "fmptdf.mm"
include "smflim2.mm"
include "eqeltrd.mm"

theorem smflimmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cS: class S
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cM: class M
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vk: setvar k
  assume smflimmpt.p: |- F/ m ph
  assume smflimmpt.x: |- F/ x ph
  assume smflimmpt.n: |- F/ n ph
  assume smflimmpt.m: |- ( ph -> M e. ZZ )
  assume smflimmpt.z: |- Z = ( ZZ>= ` M )
  assume smflimmpt.a: |- ( ( ph /\ m e. Z ) -> A e. V )
  assume smflimmpt.b: |- ( ( ph /\ m e. Z /\ x e. A ) -> B e. W )
  assume smflimmpt.s: |- ( ph -> S e. SAlg )
  assume smflimmpt.l: |- ( ( ph /\ m e. Z ) -> ( x e. A |-> B ) e. ( SMblFn ` S ) )
  assume smflimmpt.d: |- D = { x e. U_ n e. Z |^|_ m e. ( ZZ>= ` n ) A | ( m e. Z |-> B ) e. dom ~~> }
  assume smflimmpt.g: |- G = ( x e. D |-> ( ~~> ` ( m e. Z |-> B ) ) )

  disjoint A n
  disjoint A x
  disjoint n x
  disjoint B n
  disjoint S m
  disjoint S n
  disjoint m n
  disjoint Z m
  disjoint Z n
  disjoint Z x
  disjoint m x
  disjoint k x
  assert |- ( ph -> G e. ( SMblFn ` S ) )

  proof
    wph
    cG
    vx
    vm
    cZ
    vx
    cv
    #
    vm
    cv
    #
    vm
    cZ
    vx
    cA
    cB
    cmpt
    #
    cmpt
    #
    cfv
    #
    cfv
    #
    cmpt
    #
    cli
    cdm
    #
    wcel
    #
    vx
    vn
    cZ
    vm
    vn
    cv
    #
    cuz
    cfv
    #
    @4
    cdm
    #
    ciin
    #
    ciun
    #
    crab
    #
    @6
    cli
    cfv
    #
    cmpt
    #
    cS
    csmblfn
    cfv
    #
    wph
    cG
    vx
    cD
    vm
    cZ
    cB
    cmpt
    #
    cli
    cfv
    #
    cmpt
    #
    vx
    vm
    cZ
    @0
    @2
    cfv
    #
    cmpt
    #
    @7
    wcel
    #
    vx
    vn
    cZ
    vm
    @10
    @2
    cdm
    #
    ciin
    #
    ciun
    #
    crab
    #
    @22
    cli
    cfv
    #
    cmpt
    @16
    cG
    @20
    wceq
    wph
    smflimmpt.g
    a1i
    wph
    vx
    cD
    @19
    @27
    @28
    smflimmpt.x
    wph
    cD
    @18
    @7
    wcel
    #
    vx
    vn
    cZ
    vm
    @10
    cA
    ciin
    #
    ciun
    #
    crab
    #
    @27
    cD
    @32
    wceq
    wph
    smflimmpt.d
    a1i
    wph
    @29
    @23
    vx
    @31
    @26
    smflimmpt.x
    wph
    @0
    @31
    wcel
    #
    @29
    wa
    #
    @0
    @26
    wcel
    #
    @23
    wa
    #
    wph
    @34
    @36
    wph
    @34
    wa
    #
    @35
    @23
    wph
    @33
    @35
    @29
    wph
    @33
    @35
    wph
    @31
    @26
    @0
    wph
    @31
    @13
    @26
    wph
    vn
    cZ
    @30
    @12
    smflimmpt.n
    wph
    @9
    cZ
    wcel
    #
    wa
    #
    vm
    @10
    cA
    @11
    wph
    @38
    vm
    smflimmpt.p
    @38
    vm
    nfv
    #
    nfan
    #
    @39
    @1
    @10
    wcel
    #
    wa
    #
    @11
    @24
    cA
    @43
    @4
    @2
    @43
    @1
    cZ
    wcel
    #
    @2
    cvv
    wcel
    #
    @4
    @2
    wceq
    #
    @38
    @42
    @44
    wph
    cM
    @1
    @9
    cZ
    smflimmpt.z
    uztrn2
    #
    adantll
    #
    @43
    wph
    @44
    @45
    wph
    @38
    @42
    simpll
    #
    @48
    wph
    @44
    wa
    #
    vx
    cA
    cB
    cV
    smflimmpt.a
    mptexd
    #
    syl2anc
    vm
    cZ
    @2
    cvv
    @3
    @3
    eqid
    #
    fvmpt2
    #
    syl2anc
    dmeqd
    @43
    cA
    @2
    @43
    vx
    cA
    cB
    @2
    cW
    @39
    @42
    vx
    wph
    @38
    vx
    smflimmpt.x
    @38
    vx
    nfv
    nfan
    @42
    vx
    nfv
    nfan
    @43
    @0
    cA
    wcel
    #
    wa
    wph
    @44
    @54
    cB
    cW
    wcel
    #
    wph
    @38
    @42
    @54
    simplll
    @43
    @44
    @54
    @48
    adantr
    @43
    @54
    simpr
    smflimmpt.b
    syl3anc
    @2
    eqid
    #
    fnmptd
    fndmd
    eqtr2d
    iineq2d
    iuneq2df
    wph
    vn
    cZ
    @25
    @12
    smflimmpt.n
    @39
    vm
    @10
    @24
    @11
    @41
    @43
    wph
    @44
    @24
    @11
    wceq
    @49
    @48
    @50
    @2
    @4
    @50
    @4
    @2
    @50
    @44
    @45
    @46
    wph
    @44
    simpr
    @51
    @53
    syl2anc
    eqcomd
    #
    dmeqd
    syl2anc
    iineq2d
    iuneq2df
    #
    eqtr4d
    eleq2d
    #
    biimpa
    adantrr
    @37
    @0
    @30
    wcel
    #
    vn
    cZ
    wrex
    #
    @23
    wph
    @33
    @61
    @29
    @33
    @61
    wph
    @33
    @61
    vn
    @0
    cZ
    @30
    eliun
    biimpi
    #
    adantl
    adantrr
    wph
    @29
    @61
    @23
    wi
    @33
    wph
    @29
    wa
    #
    @60
    @23
    vn
    cZ
    wph
    @29
    vn
    smflimmpt.n
    @29
    vn
    nfv
    #
    nfan
    @23
    vn
    nfv
    #
    @63
    @38
    @60
    @23
    @63
    @38
    wa
    @60
    wa
    @23
    @29
    wph
    @29
    @38
    @60
    simpllr
    wph
    @38
    @60
    @23
    @29
    wb
    #
    @29
    @39
    @60
    wa
    #
    cZ
    @21
    cZ
    cB
    cvv
    vm
    @9
    cvv
    cvv
    @10
    @39
    @60
    vm
    @41
    vm
    @0
    @30
    vm
    @0
    nfcv
    vm
    @10
    cA
    nfii1
    nfel
    #
    nfan
    @38
    @9
    cz
    wcel
    #
    wph
    @60
    cM
    @9
    cZ
    smflimmpt.z
    eluzelz2
    #
    ad2antlr
    @10
    eqid
    #
    cZ
    cvv
    wcel
    #
    @67
    cZ
    cM
    cuz
    smflimmpt.z
    fvexi
    #
    a1i
    #
    @74
    @38
    @10
    cZ
    wss
    wph
    @60
    cM
    @9
    cZ
    smflimmpt.z
    uzssd3
    ad2antlr
    #
    @75
    @67
    @42
    wa
    #
    @0
    @2
    fvexd
    @76
    @54
    @55
    @21
    cB
    wceq
    #
    @60
    @42
    @54
    @39
    vm
    @0
    @10
    cA
    eliinid
    #
    adantll
    #
    @76
    wph
    @44
    @54
    @55
    @39
    @42
    wph
    @60
    @49
    adantlr
    @39
    @42
    @44
    @60
    @48
    adantlr
    @79
    smflimmpt.b
    syl3anc
    vx
    cA
    cB
    cW
    @2
    @56
    fvmpt2
    #
    syl2anc
    climeldmeqmpt3
    #
    adantllr
    mpbird
    exp31
    rexlimd
    adantrl
    mpd
    jca
    ex
    wph
    @36
    @34
    wph
    @36
    wa
    #
    @33
    @29
    wph
    @35
    @33
    @23
    wph
    @33
    @35
    @59
    biimpar
    adantrr
    #
    @82
    @61
    @29
    @82
    @33
    @61
    @83
    @62
    syl
    wph
    @23
    @61
    @29
    wi
    @35
    wph
    @23
    wa
    #
    @60
    @29
    vn
    cZ
    wph
    @23
    vn
    smflimmpt.n
    @65
    nfan
    @64
    @84
    @38
    @60
    @29
    @84
    @38
    wa
    @60
    wa
    @23
    @29
    wph
    @23
    @38
    @60
    simpllr
    wph
    @38
    @60
    @66
    @23
    @81
    adantllr
    mpbid
    exp31
    rexlimd
    adantrl
    mpd
    jca
    ex
    impbid
    rabbida3
    eqtrd
    wph
    @0
    cD
    wcel
    #
    wa
    #
    @28
    @19
    @86
    @61
    @28
    @19
    wceq
    #
    @85
    @61
    wph
    @85
    @0
    @32
    wcel
    #
    @33
    @61
    @85
    @88
    cD
    @32
    @0
    smflimmpt.d
    eleq2i
    biimpi
    @29
    vx
    @31
    rabidim1
    @62
    3syl
    adantl
    @86
    @60
    @87
    vn
    cZ
    wph
    @85
    vn
    smflimmpt.n
    vn
    @0
    cD
    vn
    @0
    nfcv
    vn
    cD
    @32
    smflimmpt.d
    @29
    vn
    vx
    @31
    @64
    vn
    cZ
    @30
    nfiu1
    nfrab
    nfcxfr
    nfel
    nfan
    @87
    vn
    nfv
    wph
    @38
    @60
    @87
    wi
    wi
    @85
    wph
    @38
    @60
    @87
    wph
    @38
    @60
    w3a
    #
    cZ
    @21
    cZ
    cB
    cvv
    vm
    @9
    cvv
    cvv
    @10
    wph
    @38
    @60
    vm
    smflimmpt.p
    @40
    @68
    nf3an
    @89
    @38
    @69
    wph
    @38
    @60
    simp2
    #
    @70
    syl
    @71
    @72
    @89
    @73
    a1i
    #
    @91
    @89
    cM
    @9
    cZ
    smflimmpt.z
    @90
    uzssd2
    #
    @92
    @89
    @42
    wa
    #
    @0
    @2
    fvexd
    @93
    @54
    @55
    @77
    @60
    wph
    @42
    @54
    @38
    @78
    3ad2antl3
    #
    @93
    wph
    @44
    @54
    @55
    wph
    @38
    @60
    @42
    simpl1
    @89
    @38
    @42
    @44
    @90
    @47
    sylan
    @94
    smflimmpt.b
    syl3anc
    @80
    syl2anc
    climfveqmpt3
    3exp
    adantr
    rexlimd
    mpd
    eqcomd
    mpteq12da
    wph
    vx
    @27
    @28
    @14
    @15
    smflimmpt.x
    wph
    @23
    @8
    vx
    @26
    @13
    smflimmpt.x
    @58
    wph
    @22
    @6
    @7
    wph
    @6
    @22
    wph
    vm
    cZ
    @5
    @21
    smflimmpt.p
    @50
    @0
    @4
    @2
    @50
    @2
    @4
    @57
    eqcomd
    fveq1d
    #
    mpteq2da
    eqcomd
    eleq1d
    rabbida2
    wph
    @22
    @6
    cli
    wph
    vm
    cZ
    @21
    @5
    smflimmpt.p
    @50
    @5
    @21
    @95
    eqcomd
    mpteq2da
    fveq2d
    mpteq12d
    3eqtrd
    wph
    vx
    @14
    cS
    vm
    vn
    @3
    @16
    cM
    cZ
    vm
    cZ
    @2
    nfmpt1
    vx
    vm
    cZ
    @2
    vx
    cZ
    nfcv
    vx
    cA
    cB
    nfmpt1
    nfmpt
    smflimmpt.m
    smflimmpt.z
    smflimmpt.s
    wph
    vm
    cZ
    @2
    @17
    @3
    smflimmpt.p
    smflimmpt.l
    @52
    fmptdf
    @14
    eqid
    @16
    eqid
    smflim2
    eqeltrd
end
