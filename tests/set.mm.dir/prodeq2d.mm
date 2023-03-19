include "wceq.mm"
include "wral.mm"
include "cprod.mm"
include "prodeq2.mm"
include "syl.mm"

theorem prodeq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume prodeq2d.1: |- ( ph -> A. k e. A B = C )

  disjoint A k
  assert |- ( ph -> prod_ k e. A B = prod_ k e. A C )

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
    cprod
    cA
    cC
    vk
    cprod
    wceq
    prodeq2d.1
    cA
    cB
    cC
    vk
    prodeq2
    syl
end
