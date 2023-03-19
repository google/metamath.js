include "wceq.mm"
include "ralrimiva.mm"
include "prodeq2d.mm"

theorem prodeq2dv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume prodeq2dv.1: |- ( ( ph /\ k e. A ) -> B = C )

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
    prodeq2dv.1
    ralrimiva
    prodeq2d
end
