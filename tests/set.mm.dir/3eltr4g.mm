include "syl5eqel.mm"
include "syl6eleqr.mm"

theorem 3eltr4g
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3eltr4g.1: |- ( ph -> A e. B )
  assume 3eltr4g.2: |- C = A
  assume 3eltr4g.3: |- D = B


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
    3eltr4g.2
    3eltr4g.1
    syl5eqel
    3eltr4g.3
    syl6eleqr
end
