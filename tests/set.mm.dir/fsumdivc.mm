include "csu.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "reccld.mm"
include "fsummulc1.mm"
include "fsumcl.mm"
include "divrecd.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "adantr.mm"
include "cc0.mm"
include "wne.mm"
include "sumeq2dv.mm"
include "3eqtr4d.mm"

theorem fsumdivc
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
  assume fsumdivc.4: |- ( ph -> C =/= 0 )

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
  assert |- ( ph -> ( sum_ k e. A B / C ) = sum_ k e. A ( B / C ) )

  proof
    wph
    cA
    cB
    vk
    csu
    #
    c1
    cC
    cdiv
    co
    #
    cmul
    co
    cA
    cB
    @1
    cmul
    co
    #
    vk
    csu
    @0
    cC
    cdiv
    co
    cA
    cB
    cC
    cdiv
    co
    #
    vk
    csu
    wph
    cA
    cB
    @1
    vk
    fsummulc2.1
    wph
    cC
    fsummulc2.2
    fsumdivc.4
    reccld
    fsummulc2.3
    fsummulc1
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
    fsumdivc.4
    divrecd
    wph
    cA
    @3
    @2
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
    @4
    fsummulc2.2
    adantr
    wph
    cC
    cc0
    wne
    @4
    fsumdivc.4
    adantr
    divrecd
    sumeq2dv
    3eqtr4d
end
