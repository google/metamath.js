include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "cmin.mm"
include "cibl.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmbf.mm"
include "iblmbf.mm"
include "syl.mm"
include "mbfmptcl.mm"
include "negsubd.mm"
include "mpteq2dva.mm"
include "cc.mm"
include "negcld.mm"
include "iblneg.mm"
include "eqeltrd.mm"
include "ibladdnc.mm"
include "eqeltrrd.mm"

theorem iblsubnc
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
  assert |- ( ph -> ( x e. A |-> ( B - C ) ) e. L^1 )

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
    cmpt
    #
    vx
    cA
    cB
    cC
    cmin
    co
    #
    cmpt
    #
    cibl
    wph
    vx
    cA
    @1
    @3
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    cB
    cC
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
    @6
    cmbf
    wcel
    ibladdnc.2
    @6
    iblmbf
    syl
    ibladdnc.1
    mbfmptcl
    #
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
    @8
    cmbf
    wcel
    ibladdnc.4
    @8
    iblmbf
    syl
    ibladdnc.3
    mbfmptcl
    #
    negsubd
    mpteq2dva
    #
    wph
    vx
    cA
    cB
    @0
    cc
    @7
    ibladdnc.2
    @5
    cC
    @9
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
    @2
    @4
    cmbf
    @10
    iblsubnc.m
    eqeltrd
    ibladdnc
    eqeltrrd
end
