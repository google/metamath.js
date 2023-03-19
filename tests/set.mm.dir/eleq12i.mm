include "wcel.mm"
include "eleq2i.mm"
include "eleq1i.mm"
include "bitri.mm"

theorem eleq12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume eleq1i.1: |- A = B
  assume eleq12i.2: |- C = D


  assert |- ( A e. C <-> B e. D )

  proof
    cA
    cC
    wcel
    cA
    cD
    wcel
    cB
    cD
    wcel
    cC
    cD
    cA
    eleq12i.2
    eleq2i
    cA
    cB
    cD
    eleq1i.1
    eleq1i
    bitri
end
