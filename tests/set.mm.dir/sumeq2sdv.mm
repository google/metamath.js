include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "adantr.mm"
include "sumeq2dv.mm"

theorem sumeq2sdv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume sumeq2sdv.1: |- ( ph -> B = C )

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
    cv
    cA
    wcel
    sumeq2sdv.1
    adantr
    sumeq2dv
end
