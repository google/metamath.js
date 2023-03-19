include "csu.mm"
include "cmul.mm"
include "co.mm"
include "fsumcl.mm"
include "fsummulc1.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "adantr.mm"
include "cc.mm"
include "adantlr.mm"
include "fsummulc2.mm"
include "sumeq2dv.mm"
include "eqtr2d.mm"

theorem fsum2mul
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  assume fsum2mul.1: |- ( ph -> A e. Fin )
  assume fsum2mul.2: |- ( ph -> B e. Fin )
  assume fsum2mul.3: |- ( ( ph /\ j e. A ) -> C e. CC )
  assume fsum2mul.4: |- ( ( ph /\ k e. B ) -> D e. CC )

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint B j
  disjoint B k
  disjoint C k
  disjoint D j
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> sum_ j e. A sum_ k e. B ( C x. D ) = ( sum_ j e. A C x. sum_ k e. B D ) )

  proof
    wph
    cA
    cC
    vj
    csu
    cB
    cD
    vk
    csu
    #
    cmul
    co
    cA
    cC
    @0
    cmul
    co
    #
    vj
    csu
    cA
    cB
    cC
    cD
    cmul
    co
    vk
    csu
    #
    vj
    csu
    wph
    cA
    cC
    @0
    vj
    fsum2mul.1
    wph
    cB
    cD
    vk
    fsum2mul.2
    fsum2mul.4
    fsumcl
    fsum2mul.3
    fsummulc1
    wph
    cA
    @1
    @2
    vj
    wph
    vj
    cv
    cA
    wcel
    #
    wa
    cB
    cD
    cC
    vk
    wph
    cB
    cfn
    wcel
    @3
    fsum2mul.2
    adantr
    fsum2mul.3
    wph
    vk
    cv
    cB
    wcel
    cD
    cc
    wcel
    @3
    fsum2mul.4
    adantlr
    fsummulc2
    sumeq2dv
    eqtr2d
end
