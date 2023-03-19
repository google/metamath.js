include "c0.mm"
include "wne.mm"
include "wss.mm"
include "cint.mm"
include "cuni.mm"
include "intssuni.mm"
include "uniss.mm"
include "sylan9ssr.mm"

theorem intssuni2
  let cA: class A
  let cB: class B


  assert |- ( ( A C_ B /\ A =/= (/) ) -> |^| A C_ U. B )

  proof
    cA
    c0
    wne
    cA
    cB
    wss
    cA
    cint
    cA
    cuni
    cB
    cuni
    cA
    intssuni
    cA
    cB
    uniss
    sylan9ssr
end
