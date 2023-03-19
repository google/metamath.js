include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cuni.mm"
include "wss.mm"
include "elssuni.mm"
include "adantl.mm"
include "wceq.mm"
include "toponuni.mm"
include "adantr.mm"
include "sseqtr4d.mm"

theorem toponss
  let cA: class A
  let cJ: class J
  let cX: class X


  assert |- ( ( J e. ( TopOn ` X ) /\ A e. J ) -> A C_ X )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cA
    cJ
    wcel
    #
    wa
    cA
    cJ
    cuni
    #
    cX
    @1
    cA
    @2
    wss
    @0
    cA
    cJ
    elssuni
    adantl
    @0
    cX
    @2
    wceq
    @1
    cX
    cJ
    toponuni
    adantr
    sseqtr4d
end
