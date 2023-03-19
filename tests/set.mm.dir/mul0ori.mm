include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "mul0or.mm"
include "mp2an.mm"

theorem mul0ori
  let cA: class A
  let cB: class B
  assume mul0or.1: |- A e. CC
  assume mul0or.2: |- B e. CC


  assert |- ( ( A x. B ) = 0 <-> ( A = 0 \/ B = 0 ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    cmul
    co
    cc0
    wceq
    cA
    cc0
    wceq
    cB
    cc0
    wceq
    wo
    wb
    mul0or.1
    mul0or.2
    cA
    cB
    mul0or
    mp2an
end
