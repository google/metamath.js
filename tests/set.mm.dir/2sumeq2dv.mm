include "csu.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "3expa.mm"
include "sumeq2dv.mm"

theorem 2sumeq2dv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  assume 2sumeq2dv.1: |- ( ( ph /\ j e. A /\ k e. B ) -> C = D )

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint B k
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> sum_ j e. A sum_ k e. B C = sum_ j e. A sum_ k e. B D )

  proof
    wph
    cA
    cB
    cC
    vk
    csu
    cB
    cD
    vk
    csu
    vj
    wph
    vj
    cv
    cA
    wcel
    #
    wa
    cB
    cC
    cD
    vk
    wph
    @0
    vk
    cv
    cB
    wcel
    cC
    cD
    wceq
    2sumeq2dv.1
    3expa
    sumeq2dv
    sumeq2dv
end
