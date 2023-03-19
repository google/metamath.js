include "eqtrd.mm"
include "eqtr2d.mm"

theorem 3eqtrrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3eqtrd.1: |- ( ph -> A = B )
  assume 3eqtrd.2: |- ( ph -> B = C )
  assume 3eqtrd.3: |- ( ph -> C = D )


  assert |- ( ph -> D = A )

  proof
    wph
    cA
    cC
    cD
    wph
    cA
    cB
    cC
    3eqtrd.1
    3eqtrd.2
    eqtrd
    3eqtrd.3
    eqtr2d
end
