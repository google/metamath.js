include "cima.mm"
include "imaeq1d.mm"
include "imaeq2d.mm"
include "eqtrd.mm"

theorem imaeq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume imaeq1d.1: |- ( ph -> A = B )
  assume imaeq12d.2: |- ( ph -> C = D )


  assert |- ( ph -> ( A " C ) = ( B " D ) )

  proof
    wph
    cA
    cC
    cima
    cB
    cC
    cima
    cB
    cD
    cima
    wph
    cA
    cB
    cC
    imaeq1d.1
    imaeq1d
    wph
    cC
    cD
    cB
    imaeq12d.2
    imaeq2d
    eqtrd
end
