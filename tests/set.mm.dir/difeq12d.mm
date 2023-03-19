include "cdif.mm"
include "difeq1d.mm"
include "difeq2d.mm"
include "eqtrd.mm"

theorem difeq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume difeq12d.1: |- ( ph -> A = B )
  assume difeq12d.2: |- ( ph -> C = D )


  assert |- ( ph -> ( A \ C ) = ( B \ D ) )

  proof
    wph
    cA
    cC
    cdif
    cB
    cC
    cdif
    cB
    cD
    cdif
    wph
    cA
    cB
    cC
    difeq12d.1
    difeq1d
    wph
    cC
    cD
    cB
    difeq12d.2
    difeq2d
    eqtrd
end
