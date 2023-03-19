include "syl5eq.mm"
include "eqtr3d.mm"

theorem 3eqtr3a
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3eqtr3a.1: |- A = B
  assume 3eqtr3a.2: |- ( ph -> A = C )
  assume 3eqtr3a.3: |- ( ph -> B = D )


  assert |- ( ph -> C = D )

  proof
    wph
    cA
    cC
    cD
    3eqtr3a.2
    wph
    cA
    cB
    cD
    3eqtr3a.1
    3eqtr3a.3
    syl5eq
    eqtr3d
end
