include "eqtr4d.mm"
include "eqtrd.mm"

theorem 3eqtr2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3eqtr2d.1: |- ( ph -> A = B )
  assume 3eqtr2d.2: |- ( ph -> C = B )
  assume 3eqtr2d.3: |- ( ph -> C = D )


  assert |- ( ph -> A = D )

  proof
    wph
    cA
    cC
    cD
    wph
    cA
    cB
    cC
    3eqtr2d.1
    3eqtr2d.2
    eqtr4d
    3eqtr2d.3
    eqtrd
end
