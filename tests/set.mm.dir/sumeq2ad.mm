include "wceq.mm"
include "ralrimivw.mm"
include "sumeq2d.mm"

theorem sumeq2ad
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume sumeq2ad.1: |- ( ph -> B = C )

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
    sumeq2ad.1
    ralrimivw
    sumeq2d
end
