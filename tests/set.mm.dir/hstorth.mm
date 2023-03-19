include "chst.mm"
include "wcel.mm"
include "cch.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "chj.mm"
include "cva.mm"
include "hstel2.mm"
include "simpld.mm"

theorem hstorth
  let cA: class A
  let cB: class B
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f


  assert |- ( ( ( S e. CHStates /\ A e. CH ) /\ ( B e. CH /\ A C_ ( _|_ ` B ) ) ) -> ( ( S ` A ) .ih ( S ` B ) ) = 0 )

  proof
    cS
    chst
    wcel
    cA
    cch
    wcel
    wa
    cB
    cch
    wcel
    cA
    cB
    cort
    cfv
    wss
    wa
    wa
    cA
    cS
    cfv
    #
    cB
    cS
    cfv
    #
    csp
    co
    cc0
    wceq
    cA
    cB
    chj
    co
    cS
    cfv
    @0
    @1
    cva
    co
    wceq
    cA
    cB
    cS
    hstel2
    simpld
end
