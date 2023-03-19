include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "adantr.mm"
include "prodeq2dv.mm"

theorem prodeq2sdv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume prodeq2sdv.1: |- ( ph -> B = C )

  disjoint A k
  disjoint k ph
  assert |- ( ph -> prod_ k e. A B = prod_ k e. A C )

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
    prodeq2sdv.1
    adantr
    prodeq2dv
end
