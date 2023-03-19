include "c1.mm"
include "cneg.mm"
include "csu.mm"
include "cmul.mm"
include "co.mm"
include "cc.mm"
include "wcel.mm"
include "neg1cn.mm"
include "a1i.mm"
include "fsummulc2.mm"
include "fsumcl.mm"
include "mulm1d.mm"
include "cv.mm"
include "wa.mm"
include "sumeq2dv.mm"
include "3eqtr3rd.mm"

theorem fsumneg
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  assume fsumneg.1: |- ( ph -> A e. Fin )
  assume fsumneg.2: |- ( ( ph /\ k e. A ) -> B e. CC )

  disjoint A k
  disjoint k ph
  assert |- ( ph -> sum_ k e. A -u B = -u sum_ k e. A B )

  proof
    wph
    c1
    cneg
    #
    cA
    cB
    vk
    csu
    #
    cmul
    co
    cA
    @0
    cB
    cmul
    co
    #
    vk
    csu
    @1
    cneg
    cA
    cB
    cneg
    #
    vk
    csu
    wph
    cA
    cB
    @0
    vk
    fsumneg.1
    @0
    cc
    wcel
    wph
    neg1cn
    a1i
    fsumneg.2
    fsummulc2
    wph
    @1
    wph
    cA
    cB
    vk
    fsumneg.1
    fsumneg.2
    fsumcl
    mulm1d
    wph
    cA
    @2
    @3
    vk
    wph
    vk
    cv
    cA
    wcel
    wa
    cB
    fsumneg.2
    mulm1d
    sumeq2dv
    3eqtr3rd
end
