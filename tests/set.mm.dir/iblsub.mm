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
include "ibladd.mm"
include "eqeltrrd.mm"

theorem iblsub
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume itgadd.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume itgadd.2: |- ( ph -> ( x e. A |-> B ) e. L^1 )
  assume itgadd.3: |- ( ( ph /\ x e. A ) -> C e. V )
  assume itgadd.4: |- ( ph -> ( x e. A |-> C ) e. L^1 )

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
    vx
    cA
    cB
    cC
    cmin
    co
    #
    cmpt
    cibl
    wph
    vx
    cA
    @1
    @2
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
    @4
    cmbf
    wcel
    itgadd.2
    @4
    iblmbf
    syl
    itgadd.1
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
    @6
    cmbf
    wcel
    itgadd.4
    @6
    iblmbf
    syl
    itgadd.3
    mbfmptcl
    #
    negsubd
    mpteq2dva
    wph
    vx
    cA
    cB
    @0
    cc
    @5
    itgadd.2
    @3
    cC
    @7
    negcld
    wph
    vx
    cA
    cC
    cV
    itgadd.3
    itgadd.4
    iblneg
    ibladd
    eqeltrrd
end
