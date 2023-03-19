include "wceq.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "wa.mm"
include "cc0.mm"
include "cc.mm"
include "wcel.mm"
include "cr.mm"
include "simp3d.mm"
include "simp1d.mm"
include "subcld.mm"
include "adantr.mm"
include "simpld.mm"
include "sigarim.mm"
include "syl2anc.mm"
include "recnd.mm"
include "mul01d.mm"
include "simp2d.mm"
include "simpr.mm"
include "subeq0bd.mm"
include "oveq2d.mm"
include "ccj.mm"
include "cfv.mm"
include "cim.mm"
include "sigarval.mm"
include "eqcomd.mm"
include "cjcld.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "0red.mm"
include "reim0d.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "mul02d.mm"
include "3eqtr4d.mm"
include "wn.mm"
include "cdiv.mm"
include "caddc.mm"
include "npncand.mm"
include "sigaraf.mm"
include "syl3anc.mm"
include "eqtr3d.mm"
include "simprd.mm"
include "sigarperm.mm"
include "addid1d.mm"
include "3eqtr2d.mm"
include "c1.mm"
include "cneg.mm"
include "negsubdi2d.mm"
include "neqned.mm"
include "subne0d.mm"
include "divnegd.mm"
include "dividd.mm"
include "negeqd.mm"
include "mulm1d.mm"
include "div32d.mm"
include "3jca.mm"
include "sigardiv.mm"
include "sigarls.mm"
include "divcld.mm"
include "mulassd.mm"
include "divcan1d.mm"
include "pm2.61dan.mm"

theorem sharhght
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cG: class G
  let vk: setvar k
  assume sharhght.sigar: |- G = ( x e. CC , y e. CC |-> ( Im ` ( ( * ` x ) x. y ) ) )
  assume sharhght.a: |- ( ph -> ( A e. CC /\ B e. CC /\ C e. CC ) )
  assume sharhght.b: |- ( ph -> ( D e. CC /\ ( ( A - D ) G ( B - D ) ) = 0 ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint k x
  assert |- ( ph -> ( ( ( C - A ) G ( D - A ) ) x. ( B - D ) ) = ( ( ( C - B ) G ( D - B ) ) x. ( A - D ) ) )

  proof
    wph
    cB
    cD
    wceq
    #
    cC
    cA
    cmin
    co
    #
    cD
    cA
    cmin
    co
    #
    cG
    co
    #
    cB
    cD
    cmin
    co
    #
    cmul
    co
    #
    cC
    cB
    cmin
    co
    #
    cD
    cB
    cmin
    co
    #
    cG
    co
    #
    cA
    cD
    cmin
    co
    #
    cmul
    co
    #
    wceq
    wph
    @0
    wa
    #
    @3
    cc0
    cmul
    co
    cc0
    @5
    @10
    @11
    @3
    @11
    @3
    @11
    @1
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    @3
    cr
    wcel
    wph
    @12
    @0
    wph
    cC
    cA
    wph
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    sharhght.a
    simp3d
    #
    wph
    @14
    @15
    @16
    sharhght.a
    simp1d
    #
    subcld
    adantr
    wph
    @13
    @0
    wph
    cD
    cA
    wph
    cD
    cc
    wcel
    #
    @9
    @4
    cG
    co
    #
    cc0
    wceq
    #
    sharhght.b
    simpld
    #
    @18
    subcld
    #
    adantr
    vx
    vy
    @1
    @2
    cG
    sharhght.sigar
    sigarim
    syl2anc
    recnd
    mul01d
    @11
    @4
    cc0
    @3
    cmul
    @11
    cB
    cD
    wph
    @15
    @0
    wph
    @14
    @15
    @16
    sharhght.a
    simp2d
    #
    adantr
    wph
    @0
    simpr
    #
    subeq0bd
    oveq2d
    @11
    @10
    cc0
    @9
    cmul
    co
    cc0
    @11
    @8
    cc0
    @9
    cmul
    @11
    @8
    @6
    ccj
    cfv
    #
    @7
    cmul
    co
    #
    cim
    cfv
    #
    cc0
    cim
    cfv
    cc0
    @11
    @6
    cc
    wcel
    #
    @7
    cc
    wcel
    #
    @8
    @28
    wceq
    wph
    @29
    @0
    wph
    cC
    cB
    @17
    @24
    subcld
    adantr
    #
    wph
    @30
    @0
    wph
    cD
    cB
    @22
    @24
    subcld
    adantr
    vx
    vy
    @6
    @7
    cG
    sharhght.sigar
    sigarval
    syl2anc
    @11
    @27
    cc0
    cim
    @11
    @27
    @26
    cc0
    cmul
    co
    cc0
    @11
    @7
    cc0
    @26
    cmul
    @11
    cD
    cB
    wph
    @19
    @0
    @22
    adantr
    #
    @11
    cB
    cD
    @25
    eqcomd
    subeq0bd
    oveq2d
    @11
    @26
    @11
    @6
    @31
    cjcld
    mul01d
    eqtrd
    fveq2d
    @11
    cc0
    @11
    0red
    reim0d
    3eqtrd
    oveq1d
    @11
    @9
    @11
    cA
    cD
    wph
    @14
    @0
    @18
    adantr
    @32
    subcld
    mul02d
    eqtrd
    3eqtr4d
    wph
    @0
    wn
    #
    wa
    #
    @5
    @8
    @9
    @4
    cdiv
    co
    #
    cmul
    co
    #
    @4
    cmul
    co
    @8
    @35
    @4
    cmul
    co
    #
    cmul
    co
    @10
    @34
    @3
    @36
    @4
    cmul
    @34
    @3
    @6
    @2
    cG
    co
    #
    @6
    @7
    @35
    cmul
    co
    #
    cG
    co
    #
    @36
    @34
    @3
    @38
    cB
    cA
    cmin
    co
    #
    @2
    cG
    co
    #
    caddc
    co
    #
    @38
    cc0
    caddc
    co
    @38
    @34
    @6
    @41
    caddc
    co
    #
    @2
    cG
    co
    #
    @3
    @43
    @34
    @44
    @1
    @2
    cG
    @34
    cC
    cB
    cA
    wph
    @16
    @33
    @17
    adantr
    #
    wph
    @15
    @33
    @24
    adantr
    #
    wph
    @14
    @33
    @18
    adantr
    #
    npncand
    oveq1d
    @34
    @29
    @13
    @41
    cc
    wcel
    @45
    @43
    wceq
    @34
    cC
    cB
    @46
    @47
    subcld
    #
    wph
    @13
    @33
    @23
    adantr
    #
    @34
    cB
    cA
    @47
    @48
    subcld
    vx
    vy
    @6
    @2
    @41
    cG
    sharhght.sigar
    sigaraf
    syl3anc
    eqtr3d
    @34
    cc0
    @42
    @38
    caddc
    @34
    @20
    cc0
    @42
    wph
    @21
    @33
    wph
    @19
    @21
    sharhght.b
    simprd
    adantr
    #
    @34
    @14
    @15
    @19
    @20
    @42
    wceq
    @48
    @47
    wph
    @19
    @33
    @22
    adantr
    #
    vx
    vy
    cA
    cB
    cD
    cG
    sharhght.sigar
    sigarperm
    syl3anc
    eqtr3d
    oveq2d
    @34
    @38
    @34
    @38
    @34
    @29
    @13
    @38
    cr
    wcel
    @49
    @50
    vx
    vy
    @6
    @2
    cG
    sharhght.sigar
    sigarim
    syl2anc
    recnd
    addid1d
    3eqtr2d
    @34
    @2
    @39
    @6
    cG
    @34
    @7
    @4
    cdiv
    co
    #
    @9
    cmul
    co
    #
    @2
    @39
    @34
    @54
    c1
    cneg
    #
    @9
    cmul
    co
    @9
    cneg
    @2
    @34
    @53
    @55
    @9
    cmul
    @34
    @53
    @4
    cneg
    #
    @4
    cdiv
    co
    @4
    @4
    cdiv
    co
    #
    cneg
    @55
    @34
    @7
    @56
    @4
    cdiv
    @34
    @56
    @7
    @34
    cB
    cD
    @47
    @52
    negsubdi2d
    eqcomd
    oveq1d
    @34
    @4
    @4
    @34
    cB
    cD
    @47
    @52
    subcld
    #
    @58
    @34
    cB
    cD
    @47
    @52
    @34
    cB
    cD
    wph
    @33
    simpr
    #
    neqned
    subne0d
    #
    divnegd
    @34
    @57
    c1
    @34
    @4
    @58
    @60
    dividd
    negeqd
    3eqtr2d
    oveq1d
    @34
    @9
    @34
    cA
    cD
    @48
    @52
    subcld
    #
    mulm1d
    @34
    cA
    cD
    @48
    @52
    negsubdi2d
    3eqtrd
    @34
    @7
    @4
    @9
    @34
    cD
    cB
    @52
    @47
    subcld
    #
    @58
    @61
    @60
    div32d
    eqtr3d
    oveq2d
    @34
    @29
    @30
    @35
    cr
    wcel
    @40
    @36
    wceq
    @49
    @62
    @34
    vx
    vy
    cD
    cA
    cB
    cG
    sharhght.sigar
    @34
    @19
    @14
    @15
    @52
    @48
    @47
    3jca
    @59
    @51
    sigardiv
    vx
    vy
    @6
    @7
    @35
    cG
    sharhght.sigar
    sigarls
    syl3anc
    3eqtrd
    oveq1d
    @34
    @8
    @35
    @4
    @34
    @29
    @30
    @8
    cc
    wcel
    @49
    @62
    @29
    @30
    wa
    @8
    vx
    vy
    @6
    @7
    cG
    sharhght.sigar
    sigarim
    recnd
    syl2anc
    @34
    @9
    @4
    @61
    @58
    @60
    divcld
    @58
    mulassd
    @34
    @37
    @9
    @8
    cmul
    @34
    @9
    @4
    @61
    @58
    @60
    divcan1d
    oveq2d
    3eqtrd
    pm2.61dan
end
