include "wceq.mm"
include "citg.mm"
include "itgeq1.mm"
include "syl.mm"

theorem itgeq1d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume itgeq1d.aeqb: |- ( ph -> A = B )

  disjoint A x
  disjoint B x
  disjoint k x
  assert |- ( ph -> S. A C _d x = S. B C _d x )

  proof
    wph
    cA
    cB
    wceq
    vx
    cA
    cC
    citg
    vx
    cB
    cC
    citg
    wceq
    itgeq1d.aeqb
    vx
    cA
    cB
    cC
    itgeq1
    syl
end
