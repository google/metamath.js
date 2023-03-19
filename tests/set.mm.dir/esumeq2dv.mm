include "nfv.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "esumeq2d.mm"

theorem esumeq2dv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume esumeq2dv.1: |- ( ( ph /\ k e. A ) -> B = C )

  disjoint k ph
  assert |- ( ph -> sum* k e. A B = sum* k e. A C )

  proof
    wph
    cA
    cB
    cC
    vk
    wph
    vk
    nfv
    wph
    cB
    cC
    wceq
    vk
    cA
    esumeq2dv.1
    ralrimiva
    esumeq2d
end
