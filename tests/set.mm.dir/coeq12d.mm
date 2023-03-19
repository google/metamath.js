include "ccom.mm"
include "coeq1d.mm"
include "coeq2d.mm"
include "eqtrd.mm"

theorem coeq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume coeq12d.1: |- ( ph -> A = B )
  assume coeq12d.2: |- ( ph -> C = D )


  assert |- ( ph -> ( A o. C ) = ( B o. D ) )

  proof
    wph
    cA
    cC
    ccom
    cB
    cC
    ccom
    cB
    cD
    ccom
    wph
    cA
    cB
    cC
    coeq12d.1
    coeq1d
    wph
    cC
    cD
    cB
    coeq12d.2
    coeq2d
    eqtrd
end
