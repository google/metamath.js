include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "adantr.mm"
include "esumeq2dv.mm"

theorem esumeq2sdv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume esumeq2sdv.1: |- ( ph -> B = C )

  disjoint k ph
  assert |- ( ph -> sum* k e. A B = sum* k e. A C )

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
    esumeq2sdv.1
    adantr
    esumeq2dv
end
