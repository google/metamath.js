include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "cxp.mm"
include "opelxpi.mm"
include "mp2an.mm"

theorem opelvv
  let cA: class A
  let cB: class B
  assume opelvv.1: |- A e. _V
  assume opelvv.2: |- B e. _V


  assert |- <. A , B >. e. ( _V X. _V )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    cop
    cvv
    cvv
    cxp
    wcel
    opelvv.1
    opelvv.2
    cA
    cB
    cvv
    cvv
    opelxpi
    mp2an
end
