include "syl5eqelr.mm"
include "syl6eleq.mm"

theorem 3eltr3g
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3eltr3g.1: |- ( ph -> A e. B )
  assume 3eltr3g.2: |- A = C
  assume 3eltr3g.3: |- B = D


  assert |- ( ph -> C e. D )

  proof
    wph
    cC
    cB
    cD
    wph
    cC
    cA
    cB
    3eltr3g.2
    3eltr3g.1
    syl5eqelr
    3eltr3g.3
    syl6eleq
end
