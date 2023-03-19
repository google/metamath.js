include "wcel.mm"
include "wss.mm"
include "cin.mm"
include "wceq.mm"
include "onelssi.mm"
include "dfss.mm"
include "sylib.mm"

theorem onelini
  let cA: class A
  let cB: class B
  assume on.1: |- A e. On


  assert |- ( B e. A -> B = ( B i^i A ) )

  proof
    cB
    cA
    wcel
    cB
    cA
    wss
    cB
    cB
    cA
    cin
    wceq
    cA
    cB
    on.1
    onelssi
    cB
    cA
    dfss
    sylib
end
