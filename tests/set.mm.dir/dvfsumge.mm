include "cmin.mm"
include "co.mm"
include "cfzo.mm"
include "csu.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "cvv.mm"
include "cicc.mm"
include "cmpt.mm"
include "cc0.mm"
include "cr.mm"
include "ccncf.mm"
include "df-neg.mm"
include "mpteq2i.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "eqid.mm"
include "subcn.mm"
include "wcel.mm"
include "cc.mm"
include "wss.mm"
include "0red.mm"
include "cuz.mm"
include "cz.mm"
include "eluzel2.mm"
include "syl.mm"
include "zred.mm"
include "eluzelz.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "a1i.mm"
include "cncfmptc.mm"
include "syl3anc.mm"
include "resubcl.mm"
include "cncfmpt2ss.mm"
include "syl5eqel.mm"
include "cv.mm"
include "cioo.mm"
include "wa.mm"
include "negex.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "ioossicc.mm"
include "sseli.mm"
include "wf.mm"
include "wral.mm"
include "cncff.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "sylan2.mm"
include "recnd.mm"
include "dvmptneg.mm"
include "wceq.mm"
include "negeqd.mm"
include "renegcld.mm"
include "c1.mm"
include "caddc.mm"
include "cxr.mm"
include "adantr.mm"
include "rexrd.mm"
include "elfzole1.mm"
include "adantl.mm"
include "iooss1.mm"
include "cfz.mm"
include "fzofzp1.mm"
include "elfzle2.mm"
include "iooss2.mm"
include "sstrd.mm"
include "sselda.mm"
include "cdv.mm"
include "cdm.mm"
include "adantlr.mm"
include "fmptd.mm"
include "ioossre.mm"
include "dvfre.mm"
include "sylancl.mm"
include "dmeqd.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "eqtrd.mm"
include "feq12d.mm"
include "mpbid.mm"
include "syldan.mm"
include "anasss.mm"
include "adantrr.mm"
include "lenegd.mm"
include "dvfsumle.mm"
include "cfn.mm"
include "fzofi.mm"
include "fsumneg.mm"
include "eluzle.mm"
include "ubicc2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "lbicc2.mm"
include "neg2subd.mm"
include "negsubdi2d.mm"
include "eqtr4d.mm"
include "3brtr3d.mm"
include "resubcld.mm"
include "fsumrecl.mm"
include "mpbird.mm"

theorem dvfsumge
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let vy: setvar y
  assume dvfsumle.m: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume dvfsumle.a: |- ( ph -> ( x e. ( M [,] N ) |-> A ) e. ( ( M [,] N ) -cn-> RR ) )
  assume dvfsumle.v: |- ( ( ph /\ x e. ( M (,) N ) ) -> B e. V )
  assume dvfsumle.b: |- ( ph -> ( RR _D ( x e. ( M (,) N ) |-> A ) ) = ( x e. ( M (,) N ) |-> B ) )
  assume dvfsumle.c: |- ( x = M -> A = C )
  assume dvfsumle.d: |- ( x = N -> A = D )
  assume dvfsumle.x: |- ( ( ph /\ k e. ( M ..^ N ) ) -> X e. RR )
  assume dvfsumge.l: |- ( ( ph /\ ( k e. ( M ..^ N ) /\ x e. ( k (,) ( k + 1 ) ) ) ) -> B <_ X )

  disjoint A k
  disjoint k x
  disjoint M k
  disjoint M x
  disjoint N k
  disjoint N x
  disjoint k ph
  disjoint ph x
  disjoint X x
  disjoint C x
  disjoint D x
  disjoint V x
  disjoint k y
  disjoint A y
  disjoint x y
  disjoint M y
  disjoint N y
  disjoint ph y
  disjoint X y
  disjoint B y
  disjoint C y
  disjoint D y
  assert |- ( ph -> ( D - C ) <_ sum_ k e. ( M ..^ N ) X )

  proof
    wph
    cD
    cC
    cmin
    co
    #
    cM
    cN
    cfzo
    co
    #
    cX
    vk
    csu
    #
    cle
    wbr
    @2
    cneg
    #
    @0
    cneg
    #
    cle
    wbr
    wph
    @1
    cX
    cneg
    #
    vk
    csu
    cD
    cneg
    #
    cC
    cneg
    #
    cmin
    co
    #
    @3
    @4
    cle
    wph
    vx
    cA
    cneg
    #
    cB
    cneg
    #
    @7
    @6
    vk
    cM
    cN
    cvv
    @5
    dvfsumle.m
    wph
    vx
    cM
    cN
    cicc
    co
    #
    @9
    cmpt
    vx
    @11
    cc0
    cA
    cmin
    co
    #
    cmpt
    @11
    cr
    ccncf
    co
    #
    vx
    @11
    @9
    @12
    cA
    df-neg
    mpteq2i
    wph
    vx
    cc0
    cA
    cr
    cmin
    ccnfld
    ctopn
    cfv
    #
    @11
    @14
    eqid
    #
    @14
    @15
    subcn
    wph
    cc0
    cr
    wcel
    @11
    cc
    wss
    cr
    cc
    wss
    #
    vx
    @11
    cc0
    cmpt
    @13
    wcel
    wph
    0red
    wph
    @11
    cr
    cc
    wph
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @11
    cr
    wss
    wph
    cM
    wph
    cN
    cM
    cuz
    cfv
    wcel
    #
    cM
    cz
    wcel
    dvfsumle.m
    cM
    cN
    eluzel2
    syl
    zred
    #
    wph
    cN
    wph
    @19
    cN
    cz
    wcel
    dvfsumle.m
    cM
    cN
    eluzelz
    syl
    zred
    #
    cM
    cN
    iccssre
    syl2anc
    ax-resscn
    syl6ss
    @16
    wph
    ax-resscn
    a1i
    vx
    cc0
    @11
    cr
    cncfmptc
    syl3anc
    dvfsumle.a
    ax-resscn
    cc0
    cA
    resubcl
    cncfmpt2ss
    syl5eqel
    @10
    cvv
    wcel
    wph
    vx
    cv
    #
    cM
    cN
    cioo
    co
    #
    wcel
    #
    wa
    #
    cB
    negex
    a1i
    wph
    vx
    cA
    cB
    cr
    cV
    @23
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    @25
    cA
    @24
    wph
    @22
    @11
    wcel
    #
    cA
    cr
    wcel
    #
    @23
    @11
    @22
    cM
    cN
    ioossicc
    sseli
    #
    wph
    @27
    vx
    @11
    wph
    @11
    cr
    vx
    @11
    cA
    cmpt
    #
    wf
    #
    @27
    vx
    @11
    wral
    #
    wph
    @29
    @13
    wcel
    @30
    dvfsumle.a
    @11
    cr
    @29
    cncff
    syl
    vx
    @11
    cr
    cA
    @29
    @29
    eqid
    fmpt
    sylibr
    #
    r19.21bi
    #
    sylan2
    recnd
    dvfsumle.v
    dvfsumle.b
    dvmptneg
    @22
    cM
    wceq
    #
    cA
    cC
    dvfsumle.c
    negeqd
    @22
    cN
    wceq
    #
    cA
    cD
    dvfsumle.d
    negeqd
    wph
    vk
    cv
    #
    @1
    wcel
    #
    wa
    #
    cX
    dvfsumle.x
    renegcld
    wph
    @37
    @22
    @36
    @36
    c1
    caddc
    co
    #
    cioo
    co
    #
    wcel
    #
    wa
    wa
    #
    cB
    cX
    cle
    wbr
    @5
    @10
    cle
    wbr
    dvfsumge.l
    @42
    cB
    cX
    wph
    @37
    @41
    cB
    cr
    wcel
    #
    @38
    @41
    @24
    @43
    @38
    @40
    @23
    @22
    @38
    @40
    cM
    @39
    cioo
    co
    #
    @23
    @38
    cM
    cxr
    wcel
    #
    cM
    @36
    cle
    wbr
    #
    @40
    @44
    wss
    @38
    cM
    wph
    @17
    @37
    @20
    adantr
    rexrd
    @37
    @46
    wph
    @36
    cM
    cN
    elfzole1
    adantl
    cM
    @36
    @39
    iooss1
    syl2anc
    @38
    cN
    cxr
    wcel
    #
    @39
    cN
    cle
    wbr
    #
    @44
    @23
    wss
    @38
    cN
    wph
    @18
    @37
    @21
    adantr
    rexrd
    @38
    @39
    cM
    cN
    cfz
    co
    wcel
    #
    @48
    @37
    @49
    wph
    cM
    cN
    @36
    fzofzp1
    adantl
    @39
    cM
    cN
    elfzle2
    syl
    cM
    @39
    cN
    iooss2
    syl2anc
    sstrd
    sselda
    @38
    @43
    vx
    @23
    @38
    @23
    cr
    vx
    @23
    cB
    cmpt
    #
    wf
    #
    @43
    vx
    @23
    wral
    @38
    cr
    vx
    @23
    cA
    cmpt
    #
    cdv
    co
    #
    cdm
    #
    cr
    @53
    wf
    #
    @51
    @38
    @23
    cr
    @52
    wf
    @23
    cr
    wss
    @55
    @38
    vx
    @23
    cA
    cr
    @52
    @24
    @38
    @26
    @27
    @28
    wph
    @26
    @27
    @37
    @33
    adantlr
    sylan2
    @52
    eqid
    fmptd
    cM
    cN
    ioossre
    @23
    @52
    dvfre
    sylancl
    @38
    @54
    @23
    cr
    @53
    @50
    wph
    @53
    @50
    wceq
    @37
    dvfsumle.b
    adantr
    #
    @38
    @54
    @50
    cdm
    #
    @23
    @38
    @53
    @50
    @56
    dmeqd
    @38
    cB
    cV
    wcel
    #
    vx
    @23
    wral
    @57
    @23
    wceq
    @38
    @58
    vx
    @23
    wph
    @24
    @58
    @37
    dvfsumle.v
    adantlr
    ralrimiva
    vx
    @23
    cB
    cV
    dmmptg
    syl
    eqtrd
    feq12d
    mpbid
    vx
    @23
    cr
    cB
    @50
    @50
    eqid
    fmpt
    sylibr
    r19.21bi
    syldan
    anasss
    wph
    @37
    cX
    cr
    wcel
    @41
    dvfsumle.x
    adantrr
    lenegd
    mpbid
    dvfsumle
    wph
    @1
    cX
    vk
    @1
    cfn
    wcel
    wph
    cM
    cN
    fzofi
    a1i
    #
    @38
    cX
    dvfsumle.x
    recnd
    fsumneg
    wph
    @8
    cC
    cD
    cmin
    co
    @4
    wph
    cD
    cC
    wph
    cD
    wph
    cN
    @11
    wcel
    #
    @31
    cD
    cr
    wcel
    #
    wph
    @45
    @47
    cM
    cN
    cle
    wbr
    #
    @60
    wph
    cM
    @20
    rexrd
    #
    wph
    cN
    @21
    rexrd
    #
    wph
    @19
    @62
    dvfsumle.m
    cM
    cN
    eluzle
    syl
    #
    cM
    cN
    ubicc2
    syl3anc
    @32
    @27
    @61
    vx
    cN
    @11
    @35
    cA
    cD
    cr
    dvfsumle.d
    eleq1d
    rspcv
    sylc
    #
    recnd
    #
    wph
    cC
    wph
    cM
    @11
    wcel
    #
    @31
    cC
    cr
    wcel
    #
    wph
    @45
    @47
    @62
    @68
    @63
    @64
    @65
    cM
    cN
    lbicc2
    syl3anc
    @32
    @27
    @69
    vx
    cM
    @11
    @34
    cA
    cC
    cr
    dvfsumle.c
    eleq1d
    rspcv
    sylc
    #
    recnd
    #
    neg2subd
    wph
    cD
    cC
    @67
    @71
    negsubdi2d
    eqtr4d
    3brtr3d
    wph
    @0
    @2
    wph
    cD
    cC
    @66
    @70
    resubcld
    wph
    @1
    cX
    vk
    @59
    dvfsumle.x
    fsumrecl
    lenegd
    mpbird
end
