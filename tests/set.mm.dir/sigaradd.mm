include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "cc.mm"
include "wcel.mm"
include "simp1d.mm"
include "simp3d.mm"
include "wceq.mm"
include "simpld.mm"
include "nnncan1d.mm"
include "oveq2d.mm"
include "simp2d.mm"
include "subcld.mm"
include "sigarms.mm"
include "syl3anc.mm"
include "eqtr3d.mm"
include "cneg.mm"
include "sigarac.mm"
include "syl2anc.mm"
include "simprd.mm"
include "negeqd.mm"
include "jca.mm"
include "sigarimcd.mm"
include "negnegd.mm"
include "neg0.mm"
include "a1i.mm"
include "3eqtr3d.mm"
include "subid1d.mm"
include "3eqtrd.mm"
include "nnncan2d.mm"
include "oveq1d.mm"
include "sigarmf.mm"
include "3eqtr2rd.mm"
include "c1.mm"
include "cmul.mm"
include "cr.mm"
include "1red.mm"
include "renegcld.mm"
include "sigarls.mm"
include "mulm1d.mm"
include "1cnd.mm"
include "negcld.mm"
include "mulcomd.mm"
include "negsubdi2d.mm"
include "3eqtr4d.mm"
include "sigarperm.mm"

theorem sigaradd
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
  assert |- ( ph -> ( ( ( B - C ) G ( A - C ) ) - ( ( D - C ) G ( A - C ) ) ) = ( ( B - C ) G ( D - C ) ) )

  proof
    wph
    cB
    cC
    cmin
    co
    #
    cA
    cC
    cmin
    co
    #
    cG
    co
    cD
    cC
    cmin
    co
    #
    @1
    cG
    co
    cmin
    co
    #
    cB
    cD
    cmin
    co
    #
    @2
    cG
    co
    #
    cC
    cD
    cmin
    co
    #
    @4
    cG
    co
    #
    @0
    @2
    cG
    co
    #
    wph
    @5
    @4
    @1
    cG
    co
    #
    @0
    @2
    cmin
    co
    #
    @1
    cG
    co
    #
    @3
    wph
    @5
    @9
    @4
    cA
    cD
    cmin
    co
    #
    cG
    co
    #
    cmin
    co
    #
    @9
    cc0
    cmin
    co
    @9
    wph
    @4
    @1
    @12
    cmin
    co
    #
    cG
    co
    #
    @5
    @14
    wph
    @15
    @2
    @4
    cG
    wph
    cA
    cC
    cD
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
    simp1d
    #
    wph
    @17
    @18
    @19
    sharhght.a
    simp3d
    #
    wph
    cD
    cc
    wcel
    #
    @12
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
    nnncan1d
    oveq2d
    wph
    @4
    cc
    wcel
    #
    @1
    cc
    wcel
    #
    @12
    cc
    wcel
    #
    @16
    @14
    wceq
    wph
    cB
    cD
    wph
    @17
    @18
    @19
    sharhght.a
    simp2d
    #
    @25
    subcld
    #
    wph
    cA
    cC
    @20
    @21
    subcld
    #
    wph
    cA
    cD
    @20
    @25
    subcld
    #
    vx
    vy
    @4
    @1
    @12
    cG
    sharhght.sigar
    sigarms
    syl3anc
    eqtr3d
    wph
    @13
    cc0
    @9
    cmin
    wph
    @13
    cneg
    #
    cneg
    cc0
    cneg
    #
    @13
    cc0
    wph
    @33
    cc0
    wph
    @23
    @33
    cc0
    wph
    @28
    @26
    @23
    @33
    wceq
    @32
    @30
    vx
    vy
    @12
    @4
    cG
    sharhght.sigar
    sigarac
    syl2anc
    wph
    @22
    @24
    sharhght.b
    simprd
    eqtr3d
    negeqd
    wph
    @13
    wph
    vx
    vy
    @4
    @12
    cG
    sharhght.sigar
    wph
    @26
    @28
    @30
    @32
    jca
    sigarimcd
    negnegd
    @34
    cc0
    wceq
    wph
    neg0
    a1i
    3eqtr3d
    oveq2d
    wph
    @9
    wph
    vx
    vy
    @4
    @1
    cG
    sharhght.sigar
    wph
    @26
    @27
    @30
    @31
    jca
    sigarimcd
    subid1d
    3eqtrd
    wph
    @10
    @4
    @1
    cG
    wph
    cB
    cD
    cC
    @29
    @25
    @21
    nnncan2d
    oveq1d
    wph
    @0
    cc
    wcel
    @27
    @2
    cc
    wcel
    @11
    @3
    wceq
    wph
    cB
    cC
    @29
    @21
    subcld
    @31
    wph
    cD
    cC
    @25
    @21
    subcld
    vx
    vy
    @0
    @1
    @2
    cG
    sharhght.sigar
    sigarmf
    syl3anc
    3eqtr2rd
    wph
    @4
    @6
    c1
    cneg
    #
    cmul
    co
    #
    cG
    co
    #
    @4
    @6
    cG
    co
    #
    @35
    cmul
    co
    #
    @5
    @7
    wph
    @26
    @6
    cc
    wcel
    #
    @35
    cr
    wcel
    @37
    @39
    wceq
    @30
    wph
    cC
    cD
    @21
    @25
    subcld
    #
    wph
    c1
    wph
    1red
    renegcld
    vx
    vy
    @4
    @6
    @35
    cG
    sharhght.sigar
    sigarls
    syl3anc
    wph
    @36
    @2
    @4
    cG
    wph
    @35
    @6
    cmul
    co
    @6
    cneg
    @36
    @2
    wph
    @6
    @41
    mulm1d
    wph
    @35
    @6
    wph
    c1
    wph
    1cnd
    negcld
    #
    @41
    mulcomd
    wph
    cC
    cD
    @21
    @25
    negsubdi2d
    3eqtr3d
    oveq2d
    wph
    @35
    @38
    cmul
    co
    @38
    cneg
    #
    @39
    @7
    wph
    @38
    wph
    vx
    vy
    @4
    @6
    cG
    sharhght.sigar
    wph
    @26
    @40
    @30
    @41
    jca
    sigarimcd
    #
    mulm1d
    wph
    @38
    @35
    @44
    @42
    mulcomd
    wph
    @40
    @26
    @7
    @43
    wceq
    @41
    @30
    vx
    vy
    @6
    @4
    cG
    sharhght.sigar
    sigarac
    syl2anc
    3eqtr4d
    3eqtr3d
    wph
    @19
    @18
    @22
    @7
    @8
    wceq
    @21
    @29
    @25
    vx
    vy
    cC
    cB
    cD
    cG
    sharhght.sigar
    sigarperm
    syl3anc
    3eqtrd
end
