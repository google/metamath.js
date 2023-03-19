include "cen.mm"
include "wbr.mm"
include "wb.mm"
include "wtru.mm"
include "cvv.mm"
include "wer.mm"
include "ener.mm"
include "a1i.mm"
include "ersymb.mm"
include "trud.mm"

theorem ensymb
  let cA: class A
  let cB: class B


  assert |- ( A ~~ B <-> B ~~ A )

  proof
    cA
    cB
    cen
    wbr
    cB
    cA
    cen
    wbr
    wb
    wtru
    cA
    cB
    cen
    cvv
    cvv
    cen
    wer
    wtru
    ener
    a1i
    ersymb
    trud
end
