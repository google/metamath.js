include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "citg.mm"
include "cmin.mm"
include "cc.mm"
include "cmpt.mm"
include "cibl.mm"
include "wcel.mm"
include "cmbf.mm"
include "iblmbf.mm"
include "syl.mm"
include "mbfmptcl.mm"
include "cv.mm"
include "wa.mm"
include "negcld.mm"
include "iblneg.mm"
include "negsubd.mm"
include "mpteq2dva.mm"
include "eqeltrd.mm"
include "itgaddnc.mm"
include "itgneg.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "itgeq2dv.mm"
include "itgcl.mm"
include "3eqtr3d.mm"

theorem itgsubnc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume ibladdnc.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume ibladdnc.2: |- ( ph -> ( x e. A |-> B ) e. L^1 )
  assume ibladdnc.3: |- ( ( ph /\ x e. A ) -> C e. V )
  assume ibladdnc.4: |- ( ph -> ( x e. A |-> C ) e. L^1 )
  assume iblsubnc.m: |- ( ph -> ( x e. A |-> ( B - C ) ) e. MblFn )

  disjoint A x
  disjoint V x
  disjoint ph x
  assert |- ( ph -> S. A ( B - C ) _d x = ( S. A B _d x - S. A C _d x ) )

  proof
    wph
    vx
    cA
    cB
    cC
    cneg
    #
    caddc
    co
    #
    citg
    #
    vx
    cA
    cB
    citg
    #
    vx
    cA
    cC
    citg
    #
    cneg
    #
    caddc
    co
    #
    vx
    cA
    cB
    cC
    cmin
    co
    #
    citg
    @3
    @4
    cmin
    co
    wph
    @2
    @3
    vx
    cA
    @0
    citg
    #
    caddc
    co
    @6
    wph
    vx
    cA
    cB
    @0
    cc
    wph
    vx
    cA
    cB
    cV
    wph
    vx
    cA
    cB
    cmpt
    #
    cibl
    wcel
    @9
    cmbf
    wcel
    ibladdnc.2
    @9
    iblmbf
    syl
    ibladdnc.1
    mbfmptcl
    #
    ibladdnc.2
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    cC
    wph
    vx
    cA
    cC
    cV
    wph
    vx
    cA
    cC
    cmpt
    #
    cibl
    wcel
    @12
    cmbf
    wcel
    ibladdnc.4
    @12
    iblmbf
    syl
    ibladdnc.3
    mbfmptcl
    #
    negcld
    wph
    vx
    cA
    cC
    cV
    ibladdnc.3
    ibladdnc.4
    iblneg
    wph
    vx
    cA
    @1
    cmpt
    vx
    cA
    @7
    cmpt
    cmbf
    wph
    vx
    cA
    @1
    @7
    @11
    cB
    cC
    @10
    @13
    negsubd
    #
    mpteq2dva
    iblsubnc.m
    eqeltrd
    itgaddnc
    wph
    @5
    @8
    @3
    caddc
    wph
    vx
    cA
    cC
    cV
    ibladdnc.3
    ibladdnc.4
    itgneg
    oveq2d
    eqtr4d
    wph
    vx
    cA
    @1
    @7
    @14
    itgeq2dv
    wph
    @3
    @4
    wph
    vx
    cA
    cB
    cV
    ibladdnc.1
    ibladdnc.2
    itgcl
    wph
    vx
    cA
    cC
    cV
    ibladdnc.3
    ibladdnc.4
    itgcl
    negsubd
    3eqtr3d
end
