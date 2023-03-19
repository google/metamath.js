include "cvv.mm"
include "wcel.mm"
include "ccnv.mm"
include "wbr.mm"
include "wb.mm"
include "brcnvg.mm"
include "mp2an.mm"

theorem brcnv
  let cA: class A
  let cB: class B
  let cR: class R
  assume opelcnv.1: |- A e. _V
  assume opelcnv.2: |- B e. _V


  assert |- ( A `' R B <-> B R A )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    cR
    ccnv
    wbr
    cB
    cA
    cR
    wbr
    wb
    opelcnv.1
    opelcnv.2
    cA
    cB
    cvv
    cvv
    cR
    brcnvg
    mp2an
end
