include "eqtrd.mm"

theorem 3eqtrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3eqtrd.1: |- ( ph -> A = B )
  assume 3eqtrd.2: |- ( ph -> B = C )
  assume 3eqtrd.3: |- ( ph -> C = D )


  assert |- ( ph -> A = D )

  proof
    wph
    cA
    cB
    cD
    3eqtrd.1
    wph
    cB
    cC
    cD
    3eqtrd.2
    3eqtrd.3
    eqtrd
    eqtrd
end
