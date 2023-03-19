include "wceq.mm"
include "ralrimivw.mm"
include "prodeq2d.mm"

theorem prodeq2ad
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume prodeq2ad.1: |- ( ph -> B = C )

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
    cA
    prodeq2ad.1
    ralrimivw
    prodeq2d
end
