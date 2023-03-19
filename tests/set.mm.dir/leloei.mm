include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "leloe.mm"
include "mp2an.mm"

theorem leloei
  let cA: class A
  let cB: class B
  assume lt.1: |- A e. RR
  assume lt.2: |- B e. RR


  assert |- ( A <_ B <-> ( A < B \/ A = B ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    cle
    wbr
    cA
    cB
    clt
    wbr
    cA
    cB
    wceq
    wo
    wb
    lt.1
    lt.2
    cA
    cB
    leloe
    mp2an
end
