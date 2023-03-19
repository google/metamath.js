include "eqtr4d.mm"

theorem 3eqtr4d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3eqtr4d.1: |- ( ph -> A = B )
  assume 3eqtr4d.2: |- ( ph -> C = A )
  assume 3eqtr4d.3: |- ( ph -> D = B )


  assert |- ( ph -> C = D )

  proof
    wph
    cC
    cA
    cD
    3eqtr4d.2
    wph
    cD
    cB
    cA
    3eqtr4d.3
    3eqtr4d.1
    eqtr4d
    eqtr4d
end
