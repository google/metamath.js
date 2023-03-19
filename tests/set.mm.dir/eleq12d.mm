include "wcel.mm"
include "eleq2d.mm"
include "eleq1d.mm"
include "bitrd.mm"

theorem eleq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume eleq12d.1: |- ( ph -> A = B )
  assume eleq12d.2: |- ( ph -> C = D )


  assert |- ( ph -> ( A e. C <-> B e. D ) )

  proof
    wph
    cA
    cC
    wcel
    cA
    cD
    wcel
    cB
    cD
    wcel
    wph
    cC
    cD
    cA
    eleq12d.2
    eleq2d
    wph
    cA
    cB
    cD
    eleq12d.1
    eleq1d
    bitrd
end
