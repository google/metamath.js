include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wb.mm"
include "lttri3.mm"
include "mp2an.mm"

theorem lttri3i
  let cA: class A
  let cB: class B
  assume lt.1: |- A e. RR
  assume lt.2: |- B e. RR


  assert |- ( A = B <-> ( -. A < B /\ -. B < A ) )

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
    clt
    wbr
    wn
    cB
    cA
    clt
    wbr
    wn
    wa
    wb
    lt.1
    lt.2
    cA
    cB
    lttri3
    mp2an
end
