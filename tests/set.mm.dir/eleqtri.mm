include "wcel.mm"
include "eleq2i.mm"
include "mpbi.mm"

theorem eleqtri
  let cA: class A
  let cB: class B
  let cC: class C
  assume eleqtr.1: |- A e. B
  assume eleqtr.2: |- B = C


  assert |- A e. C

  proof
    cA
    cB
    wcel
    cA
    cC
    wcel
    eleqtr.1
    cB
    cC
    cA
    eleqtr.2
    eleq2i
    mpbi
end
