include "wceq.mm"
include "ralrimiva.mm"
include "sumeq2d.mm"

theorem sumeq2dv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume sumeq2dv.1: |- ( ( ph /\ k e. A ) -> B = C )

  disjoint A k
  disjoint k ph
  assert |- ( ph -> sum_ k e. A B = sum_ k e. A C )

  proof
    wph
    cA
    cB
    cC
    vk
    wph
    cB
    cC
    wceq
    vk
    cA
    sumeq2dv.1
    ralrimiva
    sumeq2d
end
