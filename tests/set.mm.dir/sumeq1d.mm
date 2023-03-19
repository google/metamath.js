include "wceq.mm"
include "csu.mm"
include "sumeq1.mm"
include "syl.mm"

theorem sumeq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume sumeq1d.1: |- ( ph -> A = B )

  disjoint A k
  disjoint B k
  assert |- ( ph -> sum_ k e. A C = sum_ k e. B C )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    vk
    csu
    cB
    cC
    vk
    csu
    wceq
    sumeq1d.1
    cA
    cB
    cC
    vk
    sumeq1
    syl
end
