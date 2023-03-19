include "wceq.mm"
include "wa.mm"
include "simpl.mm"
include "simpr.mm"
include "fneq12d.mm"

theorem fneq12
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G


  assert |- ( ( F = G /\ A = B ) -> ( F Fn A <-> G Fn B ) )

  proof
    cF
    cG
    wceq
    #
    cA
    cB
    wceq
    #
    wa
    cA
    cB
    cF
    cG
    @0
    @1
    simpl
    @0
    @1
    simpr
    fneq12d
end
