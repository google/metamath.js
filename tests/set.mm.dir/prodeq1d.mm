include "wceq.mm"
include "cprod.mm"
include "prodeq1.mm"
include "syl.mm"

theorem prodeq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume prodeq1d.1: |- ( ph -> A = B )

  disjoint A k
  disjoint B k
  assert |- ( ph -> prod_ k e. A C = prod_ k e. B C )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    vk
    cprod
    cB
    cC
    vk
    cprod
    wceq
    prodeq1d.1
    cA
    cB
    cC
    vk
    prodeq1
    syl
end
