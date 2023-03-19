include "syl5eqr.mm"
include "syl6eq.mm"

theorem 3eqtr3g
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3eqtr3g.1: |- ( ph -> A = B )
  assume 3eqtr3g.2: |- A = C
  assume 3eqtr3g.3: |- B = D


  assert |- ( ph -> C = D )

  proof
    wph
    cC
    cB
    cD
    wph
    cC
    cA
    cB
    3eqtr3g.2
    3eqtr3g.1
    syl5eqr
    3eqtr3g.3
    syl6eq
end
