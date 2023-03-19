include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "csu.mm"
include "cmin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "negcld.mm"
include "fsumadd.mm"
include "fsumneg.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "negsubd.mm"
include "sumeq2dv.mm"
include "fsumcl.mm"
include "3eqtr3d.mm"

theorem fsumsub
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume fsumneg.1: |- ( ph -> A e. Fin )
  assume fsumneg.2: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume fsumsub.3: |- ( ( ph /\ k e. A ) -> C e. CC )

  disjoint A k
  disjoint k ph
  assert |- ( ph -> sum_ k e. A ( B - C ) = ( sum_ k e. A B - sum_ k e. A C ) )

  proof
    wph
    cA
    cB
    cC
    cneg
    #
    caddc
    co
    #
    vk
    csu
    #
    cA
    cB
    vk
    csu
    #
    cA
    cC
    vk
    csu
    #
    cneg
    #
    caddc
    co
    #
    cA
    cB
    cC
    cmin
    co
    #
    vk
    csu
    @3
    @4
    cmin
    co
    wph
    @2
    @3
    cA
    @0
    vk
    csu
    #
    caddc
    co
    @6
    wph
    cA
    cB
    @0
    vk
    fsumneg.1
    fsumneg.2
    wph
    vk
    cv
    cA
    wcel
    wa
    #
    cC
    fsumsub.3
    negcld
    fsumadd
    wph
    @8
    @5
    @3
    caddc
    wph
    cA
    cC
    vk
    fsumneg.1
    fsumsub.3
    fsumneg
    oveq2d
    eqtrd
    wph
    cA
    @1
    @7
    vk
    @9
    cB
    cC
    fsumneg.2
    fsumsub.3
    negsubd
    sumeq2dv
    wph
    @3
    @4
    wph
    cA
    cB
    vk
    fsumneg.1
    fsumneg.2
    fsumcl
    wph
    cA
    cC
    vk
    fsumneg.1
    fsumsub.3
    fsumcl
    negsubd
    3eqtr3d
end
