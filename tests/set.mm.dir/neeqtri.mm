include "wne.mm"
include "neeq2i.mm"
include "mpbi.mm"

theorem neeqtri
  let cA: class A
  let cB: class B
  let cC: class C
  assume neeqtr.1: |- A =/= B
  assume neeqtr.2: |- B = C


  assert |- A =/= C

  proof
    cA
    cB
    wne
    cA
    cC
    wne
    neeqtr.1
    cB
    cC
    cA
    neeqtr.2
    neeq2i
    mpbi
end
