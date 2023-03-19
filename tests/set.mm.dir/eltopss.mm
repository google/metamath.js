include "wcel.mm"
include "wss.mm"
include "ctop.mm"
include "cuni.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "adantl.mm"

theorem eltopss
  let cA: class A
  let cJ: class J
  let cX: class X
  let vx: setvar x
  assume 1open.1: |- X = U. J


  assert |- ( ( J e. Top /\ A e. J ) -> A C_ X )

  proof
    cA
    cJ
    wcel
    #
    cA
    cX
    wss
    cJ
    ctop
    wcel
    @0
    cA
    cJ
    cuni
    cX
    cA
    cJ
    elssuni
    1open.1
    syl6sseqr
    adantl
end
