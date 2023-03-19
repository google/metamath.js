include "wcel.mm"
include "cpw.mm"
include "ctop.mm"
include "cuni.mm"
include "wceq.mm"
include "ctopon.mm"
include "cfv.mm"
include "distop.mm"
include "unipw.mm"
include "eqcomi.mm"
include "a1i.mm"
include "istopon.mm"
include "sylanbrc.mm"

theorem distopon
  let cA: class A
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. V -> ~P A e. ( TopOn ` A ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cpw
    #
    ctop
    wcel
    cA
    @1
    cuni
    #
    wceq
    #
    @1
    cA
    ctopon
    cfv
    wcel
    cA
    cV
    distop
    @3
    @0
    @2
    cA
    cA
    unipw
    eqcomi
    a1i
    cA
    @1
    istopon
    sylanbrc
end
