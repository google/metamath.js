include "wceq.mm"
include "wral.mm"
include "csu.mm"
include "sumeq2.mm"
include "syl.mm"

theorem sumeq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume sumeq2d.1: |- ( ph -> A. k e. A B = C )

  disjoint A k
  assert |- ( ph -> sum_ k e. A B = sum_ k e. A C )

  proof
    wph
    cB
    cC
    wceq
    vk
    cA
    wral
    cA
    cB
    vk
    csu
    cA
    cC
    vk
    csu
    wceq
    sumeq2d.1
    cA
    cB
    cC
    vk
    sumeq2
    syl
end
