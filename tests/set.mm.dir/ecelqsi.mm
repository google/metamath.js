include "cvv.mm"
include "wcel.mm"
include "cec.mm"
include "cqs.mm"
include "ecelqsg.mm"
include "mpan.mm"

theorem ecelqsi
  let cA: class A
  let cB: class B
  let cR: class R
  assume ecelqsi.1: |- R e. _V


  assert |- ( B e. A -> [ B ] R e. ( A /. R ) )

  proof
    cR
    cvv
    wcel
    cB
    cA
    wcel
    cB
    cR
    cec
    cA
    cR
    cqs
    wcel
    ecelqsi.1
    cA
    cB
    cR
    cvv
    ecelqsg
    mpan
end
