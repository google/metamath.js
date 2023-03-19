include "con0.mm"
include "wcel.mm"
include "wss.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "onsseleq.mm"
include "mp2an.mm"

theorem onsseli
  let cA: class A
  let cB: class B
  assume on.1: |- A e. On
  assume on.2: |- B e. On


  assert |- ( A C_ B <-> ( A e. B \/ A = B ) )

  proof
    cA
    con0
    wcel
    cB
    con0
    wcel
    cA
    cB
    wss
    cA
    cB
    wcel
    cA
    cB
    wceq
    wo
    wb
    on.1
    on.2
    cA
    cB
    onsseleq
    mp2an
end
