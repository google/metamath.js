include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "ltne.mm"
include "mp2an.mm"

theorem gtneii
  let cA: class A
  let cB: class B
  assume lt.1: |- A e. RR
  assume ltneii.2: |- A < B


  assert |- B =/= A

  proof
    cA
    cr
    wcel
    cA
    cB
    clt
    wbr
    cB
    cA
    wne
    lt.1
    ltneii.2
    cA
    cB
    ltne
    mp2an
end
