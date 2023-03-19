include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wb.mm"
include "letri3.mm"
include "mp2an.mm"

theorem letri3i
  let cA: class A
  let cB: class B
  assume lt.1: |- A e. RR
  assume lt.2: |- B e. RR


  assert |- ( A = B <-> ( A <_ B /\ B <_ A ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    wceq
    cA
    cB
    cle
    wbr
    cB
    cA
    cle
    wbr
    wa
    wb
    lt.1
    lt.2
    cA
    cB
    letri3
    mp2an
end
