include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "cneg.mm"
include "cc.mm"
include "wcel.mm"
include "simp2d.mm"
include "simp1d.mm"
include "3jca.mm"
include "cc0.mm"
include "wceq.mm"
include "subcld.mm"
include "jca.mm"
include "sigariz.mm"
include "sigaradd.mm"
include "sigarperm.mm"
include "syl3anc.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "sigarimcd.mm"
include "simp3d.mm"
include "subdird.mm"
include "eqtr3d.mm"
include "sharhght.mm"
include "oveq12d.mm"
include "cr.mm"
include "sigarim.mm"
include "syl2anc.mm"
include "recnd.mm"
include "3eqtrrd.mm"
include "sigarac.mm"
include "mulneg12.mm"
include "negsubdi2d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem cevathlem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cO: class O
  let vk: setvar k
  assume cevath.sigar: |- G = ( x e. CC , y e. CC |-> ( Im ` ( ( * ` x ) x. y ) ) )
  assume cevath.a: |- ( ph -> ( A e. CC /\ B e. CC /\ C e. CC ) )
  assume cevath.b: |- ( ph -> ( F e. CC /\ D e. CC /\ E e. CC ) )
  assume cevath.c: |- ( ph -> O e. CC )
  assume cevath.d: |- ( ph -> ( ( ( A - O ) G ( D - O ) ) = 0 /\ ( ( B - O ) G ( E - O ) ) = 0 /\ ( ( C - O ) G ( F - O ) ) = 0 ) )
  assume cevath.e: |- ( ph -> ( ( ( A - F ) G ( B - F ) ) = 0 /\ ( ( B - D ) G ( C - D ) ) = 0 /\ ( ( C - E ) G ( A - E ) ) = 0 ) )
  assume cevath.f: |- ( ph -> ( ( ( A - O ) G ( B - O ) ) =/= 0 /\ ( ( B - O ) G ( C - O ) ) =/= 0 /\ ( ( C - O ) G ( A - O ) ) =/= 0 ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint O x
  disjoint O y
  disjoint E x
  disjoint E y
  disjoint F x
  disjoint F y
  disjoint k x
  assert |- ( ph -> ( ( ( C - O ) G ( A - O ) ) x. ( B - D ) ) = ( ( ( A - O ) G ( B - O ) ) x. ( D - C ) ) )

  proof
    wph
    cC
    cO
    cmin
    co
    #
    cA
    cO
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
    cB
    cO
    cmin
    co
    #
    @1
    cG
    co
    #
    cC
    cD
    cmin
    co
    #
    cmul
    co
    #
    @1
    @5
    cG
    co
    #
    cneg
    #
    @7
    cmul
    co
    #
    @9
    cD
    cC
    cmin
    co
    #
    cmul
    co
    #
    wph
    @8
    cA
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
    @7
    cmul
    co
    #
    cO
    cB
    cmin
    co
    #
    @15
    cG
    co
    #
    @7
    cmul
    co
    #
    cmin
    co
    #
    cA
    cC
    cmin
    co
    #
    @12
    cG
    co
    #
    @3
    cmul
    co
    #
    cO
    cC
    cmin
    co
    #
    @12
    cG
    co
    #
    @3
    cmul
    co
    #
    cmin
    co
    #
    @4
    wph
    @16
    @19
    cmin
    co
    #
    @7
    cmul
    co
    @8
    @21
    wph
    @29
    @6
    @7
    cmul
    wph
    @29
    @14
    @18
    cG
    co
    #
    @6
    wph
    vx
    vy
    cD
    cA
    cB
    cO
    cG
    cevath.sigar
    wph
    cD
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wph
    cF
    cc
    wcel
    @31
    cE
    cc
    wcel
    cevath.b
    simp2d
    #
    wph
    @32
    @33
    cC
    cc
    wcel
    #
    cevath.a
    simp1d
    #
    wph
    @32
    @33
    @35
    cevath.a
    simp2d
    #
    3jca
    wph
    cO
    cc
    wcel
    #
    cD
    cO
    cmin
    co
    #
    @1
    cG
    co
    cc0
    wceq
    cevath.c
    wph
    vx
    vy
    @1
    @39
    cG
    cevath.sigar
    wph
    @1
    cc
    wcel
    #
    @39
    cc
    wcel
    wph
    cA
    cO
    @36
    cevath.c
    subcld
    #
    wph
    cD
    cO
    @34
    cevath.c
    subcld
    jca
    wph
    @1
    @39
    cG
    co
    cc0
    wceq
    @5
    cE
    cO
    cmin
    co
    cG
    co
    cc0
    wceq
    @0
    cF
    cO
    cmin
    co
    cG
    co
    cc0
    wceq
    cevath.d
    simp1d
    sigariz
    jca
    #
    sigaradd
    wph
    @33
    @32
    @38
    @6
    @30
    wceq
    @37
    @36
    cevath.c
    vx
    vy
    cB
    cA
    cO
    cG
    cevath.sigar
    sigarperm
    syl3anc
    eqtr4d
    oveq1d
    wph
    @16
    @19
    @7
    wph
    vx
    vy
    @14
    @15
    cG
    cevath.sigar
    wph
    @14
    cc
    wcel
    @15
    cc
    wcel
    #
    wph
    cA
    cB
    @36
    @37
    subcld
    wph
    cD
    cB
    @34
    @37
    subcld
    #
    jca
    sigarimcd
    wph
    vx
    vy
    @18
    @15
    cG
    cevath.sigar
    wph
    @18
    cc
    wcel
    @43
    wph
    cO
    cB
    cevath.c
    @37
    subcld
    @44
    jca
    sigarimcd
    wph
    cC
    cD
    wph
    @32
    @33
    @35
    cevath.a
    simp3d
    #
    @34
    subcld
    #
    subdird
    eqtr3d
    wph
    @17
    @24
    @20
    @27
    cmin
    wph
    vx
    vy
    cB
    cC
    cA
    cD
    cG
    cevath.sigar
    wph
    @33
    @35
    @32
    @37
    @45
    @36
    3jca
    wph
    @31
    @3
    @7
    cG
    co
    cc0
    wceq
    #
    @34
    wph
    cA
    cF
    cmin
    co
    cB
    cF
    cmin
    co
    cG
    co
    cc0
    wceq
    @47
    cC
    cE
    cmin
    co
    cA
    cE
    cmin
    co
    cG
    co
    cc0
    wceq
    cevath.e
    simp2d
    jca
    #
    sharhght
    wph
    vx
    vy
    cB
    cC
    cO
    cD
    cG
    cevath.sigar
    wph
    @33
    @35
    @38
    @37
    @45
    cevath.c
    3jca
    @48
    sharhght
    oveq12d
    wph
    @23
    @26
    cmin
    co
    #
    @3
    cmul
    co
    @28
    @4
    wph
    @23
    @26
    @3
    wph
    @23
    wph
    @22
    cc
    wcel
    @12
    cc
    wcel
    #
    @23
    cr
    wcel
    wph
    cA
    cC
    @36
    @45
    subcld
    wph
    cD
    cC
    @34
    @45
    subcld
    #
    vx
    vy
    @22
    @12
    cG
    cevath.sigar
    sigarim
    syl2anc
    recnd
    wph
    vx
    vy
    @25
    @12
    cG
    cevath.sigar
    wph
    @25
    cc
    wcel
    @50
    wph
    cO
    cC
    cevath.c
    @45
    subcld
    @51
    jca
    sigarimcd
    wph
    cB
    cD
    @37
    @34
    subcld
    subdird
    wph
    @49
    @2
    @3
    cmul
    wph
    @49
    @22
    @25
    cG
    co
    #
    @2
    wph
    vx
    vy
    cD
    cA
    cC
    cO
    cG
    cevath.sigar
    wph
    @31
    @32
    @35
    @34
    @36
    @45
    3jca
    @42
    sigaradd
    wph
    @35
    @32
    @38
    @2
    @52
    wceq
    @45
    @36
    cevath.c
    vx
    vy
    cC
    cA
    cO
    cG
    cevath.sigar
    sigarperm
    syl3anc
    eqtr4d
    oveq1d
    eqtr3d
    3eqtrrd
    wph
    @6
    @10
    @7
    cmul
    wph
    @5
    cc
    wcel
    #
    @40
    @6
    @10
    wceq
    wph
    cB
    cO
    @37
    cevath.c
    subcld
    #
    @41
    vx
    vy
    @5
    @1
    cG
    cevath.sigar
    sigarac
    syl2anc
    oveq1d
    wph
    @11
    @9
    @7
    cneg
    #
    cmul
    co
    #
    @13
    wph
    @9
    cc
    wcel
    @7
    cc
    wcel
    @11
    @56
    wceq
    wph
    vx
    vy
    @1
    @5
    cG
    cevath.sigar
    wph
    @40
    @53
    @41
    @54
    jca
    sigarimcd
    @46
    @9
    @7
    mulneg12
    syl2anc
    wph
    @55
    @12
    @9
    cmul
    wph
    cC
    cD
    @45
    @34
    negsubdi2d
    oveq2d
    eqtrd
    3eqtrd
end
