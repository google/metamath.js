include "eleqtrd.mm"
include "eqeltrrd.mm"

theorem 3eltr3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3eltr3d.1: |- ( ph -> A e. B )
  assume 3eltr3d.2: |- ( ph -> A = C )
  assume 3eltr3d.3: |- ( ph -> B = D )


  assert |- ( ph -> C e. D )

  proof
    wph
    cA
    cC
    cD
    3eltr3d.2
    wph
    cA
    cB
    cD
    3eltr3d.1
    3eltr3d.3
    eleqtrd
    eqeltrrd
end
