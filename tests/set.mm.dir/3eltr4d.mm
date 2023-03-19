include "eleqtrrd.mm"
include "eqeltrd.mm"

theorem 3eltr4d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3eltr4d.1: |- ( ph -> A e. B )
  assume 3eltr4d.2: |- ( ph -> C = A )
  assume 3eltr4d.3: |- ( ph -> D = B )


  assert |- ( ph -> C e. D )

  proof
    wph
    cC
    cA
    cD
    3eltr4d.2
    wph
    cA
    cB
    cD
    3eltr4d.1
    3eltr4d.3
    eleqtrrd
    eqeltrd
end
