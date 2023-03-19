include "syl5eq.mm"
include "syl6eqr.mm"

theorem 3eqtr4g
  param wph: wff ph
  param cA: class A
  param cB: class B
  param cC: class C
  param cD: class D
  assume 3eqtr4g.1: |- ( ph -> A = B )
  assume 3eqtr4g.2: |- C = A
  assume 3eqtr4g.3: |- D = B


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
    3eqtr4g.2
    3eqtr4g.1
    syl5eq
    3eqtr4g.3
    syl6eqr
end
