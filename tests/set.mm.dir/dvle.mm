include "cmin.mm"
include "co.mm"
include "cicc.mm"
include "wcel.mm"
include "cr.mm"
include "wral.mm"
include "cmpt.mm"
include "wf.mm"
include "ccncf.mm"
include "cncff.mm"
include "syl.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "cv.mm"
include "wceq.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "resubcld.mm"
include "cle.mm"
include "caddc.mm"
include "recnd.mm"
include "subcld.mm"
include "addcomd.mm"
include "subsub2d.mm"
include "subsubd.mm"
include "3eqtr4d.mm"
include "cfv.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "subcn.mm"
include "ax-resscn.mm"
include "resubcl.mm"
include "cncfmpt2ss.mm"
include "cioo.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cdv.mm"
include "wa.mm"
include "wbr.mm"
include "cdm.mm"
include "wss.mm"
include "ioossicc.mm"
include "sseli.mm"
include "r19.21bi.mm"
include "sylan2.mm"
include "fmptd.mm"
include "ioossre.mm"
include "dvfre.mm"
include "sylancl.mm"
include "dmeqd.mm"
include "cvv.mm"
include "lerel.mm"
include "brrelex2i.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "eqtrd.mm"
include "feq12d.mm"
include "mpbid.mm"
include "brrelexi.mm"
include "subge0d.mm"
include "mpbird.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "crn.mm"
include "ctg.mm"
include "cc.mm"
include "a1i.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "tgioo2.mm"
include "cnt.mm"
include "iccntr.mm"
include "dvmptntr.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "dvmptsub.mm"
include "feq1d.mm"
include "dvge0.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt3i.mm"
include "3brtr3d.mm"
include "subled.mm"
include "eqbrtrd.mm"

theorem dvle
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  assume dvle.m: |- ( ph -> M e. RR )
  assume dvle.n: |- ( ph -> N e. RR )
  assume dvle.a: |- ( ph -> ( x e. ( M [,] N ) |-> A ) e. ( ( M [,] N ) -cn-> RR ) )
  assume dvle.b: |- ( ph -> ( RR _D ( x e. ( M (,) N ) |-> A ) ) = ( x e. ( M (,) N ) |-> B ) )
  assume dvle.c: |- ( ph -> ( x e. ( M [,] N ) |-> C ) e. ( ( M [,] N ) -cn-> RR ) )
  assume dvle.d: |- ( ph -> ( RR _D ( x e. ( M (,) N ) |-> C ) ) = ( x e. ( M (,) N ) |-> D ) )
  assume dvle.f: |- ( ( ph /\ x e. ( M (,) N ) ) -> B <_ D )
  assume dvle.x: |- ( ph -> X e. ( M [,] N ) )
  assume dvle.y: |- ( ph -> Y e. ( M [,] N ) )
  assume dvle.l: |- ( ph -> X <_ Y )
  assume dvle.p: |- ( x = X -> A = P )
  assume dvle.q: |- ( x = X -> C = Q )
  assume dvle.r: |- ( x = Y -> A = R )
  assume dvle.s: |- ( x = Y -> C = S )

  disjoint M x
  disjoint N x
  disjoint P x
  disjoint Q x
  disjoint R x
  disjoint S x
  disjoint X x
  disjoint ph x
  disjoint Y x
  assert |- ( ph -> ( R - P ) <_ ( S - Q ) )

  proof
    wph
    cR
    cS
    cQ
    cmin
    co
    #
    cP
    wph
    cY
    cM
    cN
    cicc
    co
    #
    wcel
    #
    cA
    cr
    wcel
    #
    vx
    @1
    wral
    #
    cR
    cr
    wcel
    #
    dvle.y
    wph
    @1
    cr
    vx
    @1
    cA
    cmpt
    #
    wf
    #
    @4
    wph
    @6
    @1
    cr
    ccncf
    co
    #
    wcel
    @7
    dvle.a
    @1
    cr
    @6
    cncff
    syl
    vx
    @1
    cr
    cA
    @6
    @6
    eqid
    fmpt
    sylibr
    #
    @3
    @5
    vx
    cY
    @1
    vx
    cv
    #
    cY
    wceq
    #
    cA
    cR
    cr
    dvle.r
    eleq1d
    rspcv
    sylc
    #
    wph
    cS
    cQ
    wph
    @2
    cC
    cr
    wcel
    #
    vx
    @1
    wral
    #
    cS
    cr
    wcel
    #
    dvle.y
    wph
    @1
    cr
    vx
    @1
    cC
    cmpt
    #
    wf
    #
    @14
    wph
    @16
    @8
    wcel
    @17
    dvle.c
    @1
    cr
    @16
    cncff
    syl
    vx
    @1
    cr
    cC
    @16
    @16
    eqid
    fmpt
    sylibr
    #
    @13
    @15
    vx
    cY
    @1
    @11
    cC
    cS
    cr
    dvle.s
    eleq1d
    rspcv
    sylc
    #
    wph
    cX
    @1
    wcel
    #
    @14
    cQ
    cr
    wcel
    #
    dvle.x
    @18
    @13
    @21
    vx
    cX
    @1
    @10
    cX
    wceq
    #
    cC
    cQ
    cr
    dvle.q
    eleq1d
    rspcv
    sylc
    #
    resubcld
    wph
    @20
    @4
    cP
    cr
    wcel
    #
    dvle.x
    @9
    @3
    @24
    vx
    cX
    @1
    @22
    cA
    cP
    cr
    dvle.p
    eleq1d
    rspcv
    sylc
    #
    wph
    cR
    @0
    cmin
    co
    #
    cQ
    cS
    cR
    cmin
    co
    #
    cmin
    co
    #
    cP
    cle
    wph
    cR
    cQ
    cS
    cmin
    co
    #
    caddc
    co
    @29
    cR
    caddc
    co
    @26
    @28
    wph
    cR
    @29
    wph
    cR
    @12
    recnd
    #
    wph
    cQ
    cS
    wph
    cQ
    @23
    recnd
    #
    wph
    cS
    @19
    recnd
    #
    subcld
    addcomd
    wph
    cR
    cS
    cQ
    @30
    @32
    @31
    subsub2d
    wph
    cQ
    cS
    cR
    @31
    @32
    @30
    subsubd
    3eqtr4d
    wph
    cQ
    cP
    @27
    @23
    @25
    wph
    cS
    cR
    @19
    @12
    resubcld
    wph
    cX
    vx
    @1
    cC
    cA
    cmin
    co
    #
    cmpt
    #
    cfv
    #
    cY
    @34
    cfv
    #
    cQ
    cP
    cmin
    co
    #
    @27
    cle
    wph
    cM
    cN
    @34
    cX
    cY
    dvle.m
    dvle.n
    wph
    vx
    cC
    cA
    cr
    cmin
    ccnfld
    ctopn
    cfv
    #
    @1
    @38
    eqid
    #
    @38
    @39
    subcn
    dvle.c
    dvle.a
    ax-resscn
    cC
    cA
    resubcl
    cncfmpt2ss
    wph
    cM
    cN
    cioo
    co
    #
    cc0
    cpnf
    cico
    co
    #
    cr
    @34
    cdv
    co
    #
    wf
    @40
    @41
    vx
    @40
    cD
    cB
    cmin
    co
    #
    cmpt
    #
    wf
    wph
    vx
    @40
    @43
    @41
    @44
    wph
    @10
    @40
    wcel
    #
    wa
    #
    @43
    cr
    wcel
    cc0
    @43
    cle
    wbr
    #
    @43
    @41
    wcel
    @46
    cD
    cB
    wph
    cD
    cr
    wcel
    #
    vx
    @40
    wph
    @40
    cr
    vx
    @40
    cD
    cmpt
    #
    wf
    #
    @48
    vx
    @40
    wral
    wph
    cr
    vx
    @40
    cC
    cmpt
    #
    cdv
    co
    #
    cdm
    #
    cr
    @52
    wf
    #
    @50
    wph
    @40
    cr
    @51
    wf
    @40
    cr
    wss
    #
    @54
    wph
    vx
    @40
    cC
    cr
    @51
    @45
    wph
    @10
    @1
    wcel
    #
    @13
    @40
    @1
    @10
    cM
    cN
    ioossicc
    sseli
    #
    wph
    @13
    vx
    @1
    @18
    r19.21bi
    #
    sylan2
    @51
    eqid
    fmptd
    cM
    cN
    ioossre
    #
    @40
    @51
    dvfre
    sylancl
    wph
    @53
    @40
    cr
    @52
    @49
    dvle.d
    wph
    @53
    @49
    cdm
    #
    @40
    wph
    @52
    @49
    dvle.d
    dmeqd
    wph
    cD
    cvv
    wcel
    #
    vx
    @40
    wral
    @60
    @40
    wceq
    wph
    @61
    vx
    @40
    @46
    cB
    cD
    cle
    wbr
    #
    @61
    dvle.f
    cB
    cD
    cle
    lerel
    brrelex2i
    syl
    #
    ralrimiva
    vx
    @40
    cD
    cvv
    dmmptg
    syl
    eqtrd
    feq12d
    mpbid
    vx
    @40
    cr
    cD
    @49
    @49
    eqid
    fmpt
    sylibr
    r19.21bi
    #
    wph
    cB
    cr
    wcel
    #
    vx
    @40
    wph
    @40
    cr
    vx
    @40
    cB
    cmpt
    #
    wf
    #
    @65
    vx
    @40
    wral
    wph
    cr
    vx
    @40
    cA
    cmpt
    #
    cdv
    co
    #
    cdm
    #
    cr
    @69
    wf
    #
    @67
    wph
    @40
    cr
    @68
    wf
    @55
    @71
    wph
    vx
    @40
    cA
    cr
    @68
    @45
    wph
    @56
    @3
    @57
    wph
    @3
    vx
    @1
    @9
    r19.21bi
    #
    sylan2
    @68
    eqid
    fmptd
    @59
    @40
    @68
    dvfre
    sylancl
    wph
    @70
    @40
    cr
    @69
    @66
    dvle.b
    wph
    @70
    @66
    cdm
    #
    @40
    wph
    @69
    @66
    dvle.b
    dmeqd
    wph
    cB
    cvv
    wcel
    #
    vx
    @40
    wral
    @73
    @40
    wceq
    wph
    @74
    vx
    @40
    @46
    @62
    @74
    dvle.f
    cB
    cD
    cle
    lerel
    brrelexi
    syl
    #
    ralrimiva
    vx
    @40
    cB
    cvv
    dmmptg
    syl
    eqtrd
    feq12d
    mpbid
    vx
    @40
    cr
    cB
    @66
    @66
    eqid
    fmpt
    sylibr
    r19.21bi
    #
    resubcld
    @46
    @47
    @62
    dvle.f
    @46
    cD
    cB
    @64
    @76
    subge0d
    mpbird
    @43
    elrege0
    sylanbrc
    @44
    eqid
    fmptd
    wph
    @40
    @41
    @42
    @44
    wph
    @42
    cr
    vx
    @40
    @33
    cmpt
    cdv
    co
    @44
    wph
    vx
    @33
    cr
    cioo
    crn
    ctg
    cfv
    #
    @38
    @1
    @40
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    wph
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @1
    cr
    wss
    dvle.m
    dvle.n
    cM
    cN
    iccssre
    syl2anc
    wph
    @56
    wa
    #
    @33
    @80
    cC
    cA
    @58
    @72
    resubcld
    recnd
    @38
    @39
    tgioo2
    @39
    wph
    @78
    @79
    @1
    @77
    cnt
    cfv
    cfv
    @40
    wceq
    dvle.m
    dvle.n
    cM
    cN
    iccntr
    syl2anc
    dvmptntr
    wph
    vx
    cC
    cD
    cA
    cB
    cr
    cvv
    cvv
    @40
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    @45
    wph
    @56
    cC
    cc
    wcel
    @57
    @80
    cC
    @58
    recnd
    sylan2
    @63
    dvle.d
    @45
    wph
    @56
    cA
    cc
    wcel
    @57
    @80
    cA
    @72
    recnd
    sylan2
    @75
    dvle.b
    dvmptsub
    eqtrd
    feq1d
    mpbird
    dvle.x
    dvle.y
    dvle.l
    dvge0
    wph
    @20
    @35
    @37
    wceq
    dvle.x
    vx
    cX
    @33
    @37
    @1
    @34
    @22
    cC
    cQ
    cA
    cP
    cmin
    dvle.q
    dvle.p
    oveq12d
    @34
    eqid
    #
    cC
    cA
    cmin
    ovex
    #
    fvmpt3i
    syl
    wph
    @2
    @36
    @27
    wceq
    dvle.y
    vx
    cY
    @33
    @27
    @1
    @34
    @11
    cC
    cS
    cA
    cR
    cmin
    dvle.s
    dvle.r
    oveq12d
    @81
    @82
    fvmpt3i
    syl
    3brtr3d
    subled
    eqbrtrd
    subled
end
