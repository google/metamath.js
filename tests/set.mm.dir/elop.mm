include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "csn.mm"
include "wceq.mm"
include "cpr.mm"
include "wo.mm"
include "wb.mm"
include "elopg.mm"
include "mp2an.mm"

theorem elop
  let cA: class A
  let cB: class B
  let cC: class C
  assume elop.1: |- B e. _V
  assume elop.2: |- C e. _V


  assert |- ( A e. <. B , C >. <-> ( A = { B } \/ A = { B , C } ) )

  proof
    cB
    cvv
    wcel
    cC
    cvv
    wcel
    cA
    cB
    cC
    cop
    wcel
    cA
    cB
    csn
    wceq
    cA
    cB
    cC
    cpr
    wceq
    wo
    wb
    elop.1
    elop.2
    cB
    cC
    cA
    cvv
    cvv
    elopg
    mp2an
end
