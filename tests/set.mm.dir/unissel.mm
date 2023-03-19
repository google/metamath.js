include "cuni.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "simpl.mm"
include "elssuni.mm"
include "adantl.mm"
include "eqssd.mm"

theorem unissel
  let cA: class A
  let cB: class B


  assert |- ( ( U. A C_ B /\ B e. A ) -> U. A = B )

  proof
    cA
    cuni
    #
    cB
    wss
    #
    cB
    cA
    wcel
    #
    wa
    @0
    cB
    @1
    @2
    simpl
    @2
    cB
    @0
    wss
    @1
    cB
    cA
    elssuni
    adantl
    eqssd
end
