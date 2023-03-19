include "eqtr4d.mm"

theorem 3eqtr4rd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3eqtr4d.1: |- ( ph -> A = B )
  assume 3eqtr4d.2: |- ( ph -> C = A )
  assume 3eqtr4d.3: |- ( ph -> D = B )


  assert |- ( ph -> D = C )

  proof
    wph
    cD
    cA
    cC
    wph
    cD
    cB
    cA
    3eqtr4d.3
    3eqtr4d.1
    eqtr4d
    3eqtr4d.2
    eqtr4d
end
