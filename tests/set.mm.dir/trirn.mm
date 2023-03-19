include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "csqrt.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "resqcld.mm"
include "cr.mm"
include "2re.mm"
include "remulcld.mm"
include "remulcl.mm"
include "sylancr.mm"
include "readdcld.mm"
include "fsumrecl.mm"
include "sqge0d.mm"
include "fsumge0.mm"
include "mulge0d.mm"
include "resqrtcld.mm"
include "recnd.mm"
include "fsumadd.mm"
include "2cnd.mm"
include "fsummulc2.mm"
include "cabs.mm"
include "abscld.mm"
include "leabsd.mm"
include "csbren.mm"
include "wceq.mm"
include "absresq.mm"
include "syl.mm"
include "cc0.mm"
include "resqrtth.mm"
include "syl2anc.mm"
include "3brtr4d.mm"
include "absge0d.mm"
include "sqrtge0d.mm"
include "le2sqd.mm"
include "mpbird.mm"
include "letrd.mm"
include "clt.mm"
include "wb.mm"
include "a1i.mm"
include "2pos.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "eqbrtrrd.mm"
include "leadd2dd.mm"
include "eqbrtrd.mm"
include "leadd1dd.mm"
include "cc.mm"
include "binom2.mm"
include "sumeq2dv.mm"
include "eqtrd.mm"
include "sqrtmuld.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "addge0d.mm"

theorem trirn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vx: setvar x
  assume csbrn.1: |- ( ph -> A e. Fin )
  assume csbrn.2: |- ( ( ph /\ k e. A ) -> B e. RR )
  assume csbrn.3: |- ( ( ph /\ k e. A ) -> C e. RR )

  disjoint A k
  disjoint k ph
  disjoint k x
  disjoint A x
  disjoint B x
  disjoint C x
  disjoint ph x
  assert |- ( ph -> ( sqrt ` sum_ k e. A ( ( B + C ) ^ 2 ) ) <_ ( ( sqrt ` sum_ k e. A ( B ^ 2 ) ) + ( sqrt ` sum_ k e. A ( C ^ 2 ) ) ) )

  proof
    wph
    cA
    cB
    cC
    caddc
    co
    #
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    #
    cA
    cB
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    #
    cA
    cC
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    @3
    c2
    cexp
    co
    #
    @10
    c2
    cexp
    co
    #
    cle
    wbr
    wph
    cA
    @4
    c2
    cB
    cC
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    vk
    csu
    #
    @8
    caddc
    co
    #
    @5
    c2
    @5
    @8
    cmul
    co
    #
    csqrt
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @8
    caddc
    co
    #
    @11
    @12
    cle
    wph
    @16
    @21
    @8
    wph
    cA
    @15
    vk
    csbrn.1
    wph
    vk
    cv
    cA
    wcel
    wa
    #
    @4
    @14
    @23
    cB
    csbrn.2
    resqcld
    #
    @23
    c2
    cr
    wcel
    #
    @13
    cr
    wcel
    @14
    cr
    wcel
    2re
    @23
    cB
    cC
    csbrn.2
    csbrn.3
    remulcld
    #
    c2
    @13
    remulcl
    sylancr
    #
    readdcld
    #
    fsumrecl
    wph
    @5
    @20
    wph
    cA
    @4
    vk
    csbrn.1
    @24
    fsumrecl
    #
    wph
    @25
    @19
    cr
    wcel
    #
    @20
    cr
    wcel
    2re
    wph
    @18
    wph
    @5
    @8
    @29
    wph
    cA
    @7
    vk
    csbrn.1
    @23
    cC
    csbrn.3
    resqcld
    #
    fsumrecl
    #
    remulcld
    #
    wph
    @5
    @8
    @29
    @32
    wph
    cA
    @4
    vk
    csbrn.1
    @24
    @23
    cB
    csbrn.2
    sqge0d
    fsumge0
    #
    wph
    cA
    @7
    vk
    csbrn.1
    @31
    @23
    cC
    csbrn.3
    sqge0d
    fsumge0
    #
    mulge0d
    #
    resqrtcld
    #
    c2
    @19
    remulcl
    sylancr
    #
    readdcld
    @32
    wph
    @16
    @5
    cA
    @14
    vk
    csu
    #
    caddc
    co
    @21
    cle
    wph
    cA
    @4
    @14
    vk
    csbrn.1
    @23
    @4
    @24
    recnd
    @23
    @14
    @27
    recnd
    fsumadd
    wph
    @39
    @20
    @5
    wph
    cA
    @14
    vk
    csbrn.1
    @27
    fsumrecl
    @38
    @29
    wph
    c2
    cA
    @13
    vk
    csu
    #
    cmul
    co
    #
    @39
    @20
    cle
    wph
    cA
    @13
    c2
    vk
    csbrn.1
    wph
    2cnd
    @23
    @13
    @26
    recnd
    fsummulc2
    wph
    @40
    @19
    cle
    wbr
    #
    @41
    @20
    cle
    wbr
    #
    wph
    @40
    @40
    cabs
    cfv
    #
    @19
    wph
    cA
    @13
    vk
    csbrn.1
    @26
    fsumrecl
    #
    wph
    @40
    wph
    @40
    @45
    recnd
    #
    abscld
    #
    @37
    wph
    @40
    @45
    leabsd
    wph
    @44
    @19
    cle
    wbr
    @44
    c2
    cexp
    co
    #
    @19
    c2
    cexp
    co
    #
    cle
    wbr
    wph
    @40
    c2
    cexp
    co
    #
    @18
    @48
    @49
    cle
    wph
    cA
    cB
    cC
    vk
    csbrn.1
    csbrn.2
    csbrn.3
    csbren
    wph
    @40
    cr
    wcel
    #
    @48
    @50
    wceq
    @45
    @40
    absresq
    syl
    wph
    @18
    cr
    wcel
    cc0
    @18
    cle
    wbr
    @49
    @18
    wceq
    @33
    @36
    @18
    resqrtth
    syl2anc
    3brtr4d
    wph
    @44
    @19
    @47
    @37
    wph
    @40
    @46
    absge0d
    wph
    @18
    @33
    @36
    sqrtge0d
    le2sqd
    mpbird
    letrd
    wph
    @51
    @30
    @25
    cc0
    c2
    clt
    wbr
    #
    @42
    @43
    wb
    @45
    @37
    @25
    wph
    2re
    a1i
    @52
    wph
    2pos
    a1i
    @40
    @19
    c2
    lemul2
    syl112anc
    mpbid
    eqbrtrrd
    leadd2dd
    eqbrtrd
    leadd1dd
    wph
    @11
    @2
    @17
    wph
    @2
    cr
    wcel
    cc0
    @2
    cle
    wbr
    @11
    @2
    wceq
    wph
    cA
    @1
    vk
    csbrn.1
    @23
    @0
    @23
    cB
    cC
    csbrn.2
    csbrn.3
    readdcld
    #
    resqcld
    #
    fsumrecl
    #
    wph
    cA
    @1
    vk
    csbrn.1
    @54
    @23
    @0
    @53
    sqge0d
    fsumge0
    #
    @2
    resqrtth
    syl2anc
    wph
    @2
    cA
    @15
    @7
    caddc
    co
    #
    vk
    csu
    @17
    wph
    cA
    @1
    @57
    vk
    @23
    cB
    cc
    wcel
    cC
    cc
    wcel
    @1
    @57
    wceq
    @23
    cB
    csbrn.2
    recnd
    @23
    cC
    csbrn.3
    recnd
    cB
    cC
    binom2
    syl2anc
    sumeq2dv
    wph
    cA
    @15
    @7
    vk
    csbrn.1
    @23
    @15
    @28
    recnd
    @23
    @7
    @31
    recnd
    fsumadd
    eqtrd
    eqtrd
    wph
    @12
    @6
    c2
    cexp
    co
    #
    c2
    @6
    @9
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @9
    c2
    cexp
    co
    #
    caddc
    co
    #
    @22
    wph
    @6
    cc
    wcel
    @9
    cc
    wcel
    @12
    @63
    wceq
    wph
    @6
    wph
    @5
    @29
    @34
    resqrtcld
    #
    recnd
    wph
    @9
    wph
    @8
    @32
    @35
    resqrtcld
    #
    recnd
    @6
    @9
    binom2
    syl2anc
    wph
    @61
    @21
    @62
    @8
    caddc
    wph
    @58
    @5
    @60
    @20
    caddc
    wph
    @5
    cr
    wcel
    cc0
    @5
    cle
    wbr
    @58
    @5
    wceq
    @29
    @34
    @5
    resqrtth
    syl2anc
    wph
    @59
    @19
    c2
    cmul
    wph
    @19
    @59
    wph
    @5
    @8
    @29
    @34
    @32
    @35
    sqrtmuld
    eqcomd
    oveq2d
    oveq12d
    wph
    @8
    cr
    wcel
    cc0
    @8
    cle
    wbr
    @62
    @8
    wceq
    @32
    @35
    @8
    resqrtth
    syl2anc
    oveq12d
    eqtrd
    3brtr4d
    wph
    @3
    @10
    wph
    @2
    @55
    @56
    resqrtcld
    wph
    @6
    @9
    @64
    @65
    readdcld
    wph
    @2
    @55
    @56
    sqrtge0d
    wph
    @6
    @9
    @64
    @65
    wph
    @5
    @29
    @34
    sqrtge0d
    wph
    @8
    @32
    @35
    sqrtge0d
    addge0d
    le2sqd
    mpbird
end
