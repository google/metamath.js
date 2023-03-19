include "eqtr3d.mm"

theorem 3eqtr3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3eqtr3d.1: |- ( ph -> A = B )
  assume 3eqtr3d.2: |- ( ph -> A = C )
  assume 3eqtr3d.3: |- ( ph -> B = D )


  assert |- ( ph -> C = D )

  proof
    wph
    cB
    cC
    cD
    wph
    cA
    cB
    cC
    3eqtr3d.1
    3eqtr3d.2
    eqtr3d
    3eqtr3d.3
    eqtr3d
end
