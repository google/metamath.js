include "wcel.mm"
include "wss.mm"
include "cun.mm"
include "wceq.mm"
include "onelssi.mm"
include "ssequn2.mm"
include "sylib.mm"

theorem oneluni
  let cA: class A
  let cB: class B
  assume on.1: |- A e. On


  assert |- ( B e. A -> ( A u. B ) = A )

  proof
    cB
    cA
    wcel
    cB
    cA
    wss
    cA
    cB
    cun
    cA
    wceq
    cA
    cB
    on.1
    onelssi
    cB
    cA
    ssequn2
    sylib
end
