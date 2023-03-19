include "csu.mm"
include "cmul.mm"
include "co.mm"
include "fsummulc2.mm"
include "fsumcl.mm"
include "mulcomd.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "adantr.mm"
include "sumeq2dv.mm"
include "3eqtr4d.mm"

theorem fsummulc1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  assume fsummulc2.1: |- ( ph -> A e. Fin )
  assume fsummulc2.2: |- ( ph -> C e. CC )
  assume fsummulc2.3: |- ( ( ph /\ k e. A ) -> B e. CC )

  disjoint A k
  disjoint C k
  disjoint k ph
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint A f
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint A m
  disjoint A n
  disjoint B f
  disjoint B m
  disjoint B n
  disjoint C f
  disjoint C m
  disjoint C n
  disjoint f ph
  disjoint m ph
  disjoint n ph
  assert |- ( ph -> ( sum_ k e. A B x. C ) = sum_ k e. A ( B x. C ) )

  proof
    wph
    cC
    cA
    cB
    vk
    csu
    #
    cmul
    co
    cA
    cC
    cB
    cmul
    co
    #
    vk
    csu
    @0
    cC
    cmul
    co
    cA
    cB
    cC
    cmul
    co
    #
    vk
    csu
    wph
    cA
    cB
    cC
    vk
    fsummulc2.1
    fsummulc2.2
    fsummulc2.3
    fsummulc2
    wph
    @0
    cC
    wph
    cA
    cB
    vk
    fsummulc2.1
    fsummulc2.3
    fsumcl
    fsummulc2.2
    mulcomd
    wph
    cA
    @2
    @1
    vk
    wph
    vk
    cv
    cA
    wcel
    #
    wa
    cB
    cC
    fsummulc2.3
    wph
    cC
    cc
    wcel
    @3
    fsummulc2.2
    adantr
    mulcomd
    sumeq2dv
    3eqtr4d
end
