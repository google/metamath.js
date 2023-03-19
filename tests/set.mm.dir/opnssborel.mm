include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "crrx.mm"
include "cfv.mm"
include "ctopn.mm"
include "fvex.mm"
include "eqeltri.mm"
include "sssalgen.mm"
include "ax-mp.mm"

theorem opnssborel
  let cA: class A
  let cB: class B
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume opnssborel.a: |- A = ( TopOpen ` ( RR^ ` X ) )
  assume opnssborel.b: |- B = ( SalGen ` A )


  assert |- A C_ B

  proof
    cA
    cvv
    wcel
    cA
    cB
    wss
    cA
    cX
    crrx
    cfv
    #
    ctopn
    cfv
    cvv
    opnssborel.a
    @0
    ctopn
    fvex
    eqeltri
    cB
    cvv
    cA
    opnssborel.b
    sssalgen
    ax-mp
end
