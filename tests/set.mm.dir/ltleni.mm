include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wne.mm"
include "wa.mm"
include "wb.mm"
include "ltlen.mm"
include "mp2an.mm"

theorem ltleni
  let cA: class A
  let cB: class B
  assume lt.1: |- A e. RR
  assume lt.2: |- B e. RR


  assert |- ( A < B <-> ( A <_ B /\ B =/= A ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    clt
    wbr
    cA
    cB
    cle
    wbr
    cB
    cA
    wne
    wa
    wb
    lt.1
    lt.2
    cA
    cB
    ltlen
    mp2an
end
