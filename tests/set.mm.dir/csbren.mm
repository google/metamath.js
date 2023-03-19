include "cmul.mm"
include "co.mm"
include "csu.mm"
include "c2.mm"
include "cexp.mm"
include "cle.mm"
include "wbr.mm"
include "c4.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "2cn.mm"
include "cv.mm"
include "wa.mm"
include "remulcld.mm"
include "fsumrecl.mm"
include "recnd.mm"
include "sqmul.mm"
include "sylancr.mm"
include "sq2.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "cmin.mm"
include "cc0.mm"
include "resqcld.mm"
include "cr.mm"
include "2re.mm"
include "remulcl.mm"
include "caddc.mm"
include "cfn.mm"
include "adantr.mm"
include "adantlr.mm"
include "simplr.mm"
include "readdcld.mm"
include "sqge0d.mm"
include "binom2.mm"
include "syl2anc.mm"
include "sqmuld.mm"
include "mul32d.mm"
include "oveq2d.mm"
include "2cnd.mm"
include "mulassd.mm"
include "eqtr4d.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "fsumge0.mm"
include "addcld.mm"
include "fsumadd.mm"
include "simpr.mm"
include "sqcld.mm"
include "fsummulc1.mm"
include "fsummulc2.mm"
include "discr.mm"
include "4re.mm"
include "suble0d.mm"
include "mpbid.mm"
include "eqbrtrrd.mm"
include "clt.mm"
include "wb.mm"
include "a1i.mm"
include "4pos.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "mpbird.mm"

theorem csbren
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
  assert |- ( ph -> ( sum_ k e. A ( B x. C ) ^ 2 ) <_ ( sum_ k e. A ( B ^ 2 ) x. sum_ k e. A ( C ^ 2 ) ) )

  proof
    wph
    cA
    cB
    cC
    cmul
    co
    #
    vk
    csu
    #
    c2
    cexp
    co
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
    cA
    cC
    c2
    cexp
    co
    #
    vk
    csu
    #
    cmul
    co
    #
    cle
    wbr
    #
    c4
    @2
    cmul
    co
    #
    c4
    @7
    cmul
    co
    #
    cle
    wbr
    #
    wph
    c2
    @1
    cmul
    co
    #
    c2
    cexp
    co
    #
    @9
    @10
    cle
    wph
    @13
    c2
    c2
    cexp
    co
    #
    @2
    cmul
    co
    #
    @9
    wph
    c2
    cc
    wcel
    @1
    cc
    wcel
    @13
    @15
    wceq
    2cn
    wph
    @1
    wph
    cA
    @0
    vk
    csbrn.1
    wph
    vk
    cv
    cA
    wcel
    #
    wa
    #
    cB
    cC
    csbrn.2
    csbrn.3
    remulcld
    #
    fsumrecl
    #
    recnd
    c2
    @1
    sqmul
    sylancr
    @14
    c4
    @2
    cmul
    sq2
    oveq1i
    syl6eq
    wph
    @13
    @10
    cmin
    co
    cc0
    cle
    wbr
    @13
    @10
    cle
    wbr
    wph
    vx
    @4
    @12
    @6
    wph
    cA
    @3
    vk
    csbrn.1
    @17
    cB
    csbrn.2
    resqcld
    #
    fsumrecl
    #
    wph
    c2
    cr
    wcel
    #
    @1
    cr
    wcel
    @12
    cr
    wcel
    2re
    @19
    c2
    @1
    remulcl
    sylancr
    #
    wph
    cA
    @5
    vk
    csbrn.1
    @17
    cC
    csbrn.3
    resqcld
    #
    fsumrecl
    #
    wph
    vx
    cv
    #
    cr
    wcel
    #
    wa
    #
    cc0
    cA
    @3
    @26
    c2
    cexp
    co
    #
    cmul
    co
    #
    c2
    @0
    cmul
    co
    #
    @26
    cmul
    co
    #
    caddc
    co
    #
    @5
    caddc
    co
    #
    vk
    csu
    #
    @4
    @29
    cmul
    co
    #
    @12
    @26
    cmul
    co
    #
    caddc
    co
    #
    @6
    caddc
    co
    #
    cle
    @28
    cA
    @34
    vk
    wph
    cA
    cfn
    wcel
    @27
    csbrn.1
    adantr
    #
    @28
    @16
    wa
    #
    @33
    @5
    @41
    @30
    @32
    @41
    @3
    @29
    wph
    @16
    @3
    cr
    wcel
    @27
    @20
    adantlr
    #
    @41
    @26
    wph
    @27
    @16
    simplr
    #
    resqcld
    remulcld
    #
    @41
    @31
    @26
    wph
    @16
    @31
    cr
    wcel
    #
    @27
    @17
    @22
    @0
    cr
    wcel
    #
    @45
    2re
    @18
    c2
    @0
    remulcl
    sylancr
    #
    adantlr
    @43
    remulcld
    #
    readdcld
    wph
    @16
    @5
    cr
    wcel
    @27
    @24
    adantlr
    #
    readdcld
    @41
    cc0
    cB
    @26
    cmul
    co
    #
    cC
    caddc
    co
    #
    c2
    cexp
    co
    #
    @34
    cle
    @41
    @51
    @41
    @50
    cC
    @41
    cB
    @26
    wph
    @16
    cB
    cr
    wcel
    @27
    csbrn.2
    adantlr
    #
    @43
    remulcld
    #
    wph
    @16
    cC
    cr
    wcel
    @27
    csbrn.3
    adantlr
    #
    readdcld
    sqge0d
    @41
    @52
    @50
    c2
    cexp
    co
    #
    c2
    @50
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
    @5
    caddc
    co
    #
    @34
    @41
    @50
    cc
    wcel
    cC
    cc
    wcel
    @52
    @60
    wceq
    @41
    @50
    @54
    recnd
    @41
    cC
    @55
    recnd
    #
    @50
    cC
    binom2
    syl2anc
    @41
    @59
    @33
    @5
    caddc
    @41
    @56
    @30
    @58
    @32
    caddc
    @41
    cB
    @26
    @41
    cB
    @53
    recnd
    #
    @41
    @26
    @43
    recnd
    #
    sqmuld
    @41
    @58
    c2
    @0
    @26
    cmul
    co
    #
    cmul
    co
    @32
    @41
    @57
    @64
    c2
    cmul
    @41
    cB
    @26
    cC
    @62
    @63
    @61
    mul32d
    oveq2d
    @41
    c2
    @0
    @26
    @41
    2cnd
    @41
    @0
    wph
    @16
    @46
    @27
    @18
    adantlr
    recnd
    #
    @63
    mulassd
    eqtr4d
    oveq12d
    oveq1d
    eqtrd
    breqtrd
    fsumge0
    @28
    @35
    cA
    @33
    vk
    csu
    #
    @6
    caddc
    co
    @39
    @28
    cA
    @33
    @5
    vk
    @40
    @41
    @30
    @32
    @41
    @30
    @44
    recnd
    #
    @41
    @32
    @48
    recnd
    #
    addcld
    @41
    @5
    @49
    recnd
    fsumadd
    @28
    @66
    @38
    @6
    caddc
    @28
    @66
    cA
    @30
    vk
    csu
    #
    cA
    @32
    vk
    csu
    #
    caddc
    co
    @38
    @28
    cA
    @30
    @32
    vk
    @40
    @67
    @68
    fsumadd
    @28
    @36
    @69
    @37
    @70
    caddc
    @28
    cA
    @3
    @29
    vk
    @40
    @28
    @26
    @28
    @26
    wph
    @27
    simpr
    recnd
    #
    sqcld
    @41
    @3
    @42
    recnd
    fsummulc1
    @28
    @37
    cA
    @31
    vk
    csu
    #
    @26
    cmul
    co
    @70
    @28
    @12
    @72
    @26
    cmul
    @28
    cA
    @0
    c2
    vk
    @40
    @28
    2cnd
    @65
    fsummulc2
    oveq1d
    @28
    cA
    @31
    @26
    vk
    @40
    @71
    wph
    @16
    @31
    cc
    wcel
    @27
    @17
    @31
    @47
    recnd
    adantlr
    fsummulc1
    eqtrd
    oveq12d
    eqtr4d
    oveq1d
    eqtrd
    breqtrd
    discr
    wph
    @13
    @10
    wph
    @12
    @23
    resqcld
    wph
    c4
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    @10
    cr
    wcel
    4re
    wph
    @4
    @6
    @21
    @25
    remulcld
    #
    c4
    @7
    remulcl
    sylancr
    suble0d
    mpbid
    eqbrtrrd
    wph
    @2
    cr
    wcel
    @74
    @73
    cc0
    c4
    clt
    wbr
    #
    @8
    @11
    wb
    wph
    @1
    @19
    resqcld
    @75
    @73
    wph
    4re
    a1i
    @76
    wph
    4pos
    a1i
    @2
    @7
    c4
    lemul2
    syl112anc
    mpbird
end
