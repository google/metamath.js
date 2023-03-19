include "syl6eq.mm"
include "eqtr4d.mm"

theorem 3eqtr4a
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3eqtr4a.1: |- A = B
  assume 3eqtr4a.2: |- ( ph -> C = A )
  assume 3eqtr4a.3: |- ( ph -> D = B )


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
    3eqtr4a.2
    3eqtr4a.1
    syl6eq
    3eqtr4a.3
    eqtr4d
end
