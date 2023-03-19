include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "ccnv.mm"
include "wb.mm"
include "opelcnvg.mm"
include "mp2an.mm"

theorem opelcnv
  let cA: class A
  let cB: class B
  let cR: class R
  assume opelcnv.1: |- A e. _V
  assume opelcnv.2: |- B e. _V


  assert |- ( <. A , B >. e. `' R <-> <. B , A >. e. R )

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
    cR
    ccnv
    wcel
    cB
    cA
    cop
    cR
    wcel
    wb
    opelcnv.1
    opelcnv.2
    cA
    cB
    cvv
    cvv
    cR
    opelcnvg
    mp2an
end
