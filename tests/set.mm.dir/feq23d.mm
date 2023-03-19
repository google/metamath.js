include "eqidd.mm"
include "feq123d.mm"

theorem feq23d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  assume feq23d.1: |- ( ph -> A = C )
  assume feq23d.2: |- ( ph -> B = D )


  assert |- ( ph -> ( F : A --> B <-> F : C --> D ) )

  proof
    wph
    cA
    cC
    cB
    cD
    cF
    cF
    wph
    cF
    eqidd
    feq23d.1
    feq23d.2
    feq123d
end
