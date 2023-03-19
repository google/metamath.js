include "wne.mm"
include "neeq1i.mm"
include "mpbir.mm"

theorem eqnetri
  let cA: class A
  let cB: class B
  let cC: class C
  assume eqnetr.1: |- A = B
  assume eqnetr.2: |- B =/= C


  assert |- A =/= C

  proof
    cA
    cC
    wne
    cB
    cC
    wne
    eqnetr.2
    cA
    cB
    cC
    eqnetr.1
    neeq1i
    mpbir
end
