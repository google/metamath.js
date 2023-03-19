include "cfin3.mm"
include "wcel.mm"
include "cv.mm"
include "cpw.mm"
include "cfin4.mm"
include "cab.mm"
include "df-fin3.mm"
include "eleq2i.mm"
include "pwexr.mm"
include "wceq.mm"
include "pweq.mm"
include "eleq1d.mm"
include "elab3.mm"
include "bitri.mm"

theorem isfin3
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cX: class X


  assert |- ( A e. Fin3 <-> ~P A e. Fin4 )

  proof
    cA
    cfin3
    wcel
    cA
    vx
    cv
    #
    cpw
    #
    cfin4
    wcel
    #
    vx
    cab
    #
    wcel
    cA
    cpw
    #
    cfin4
    wcel
    #
    cfin3
    @3
    cA
    vx
    df-fin3
    eleq2i
    @2
    @5
    vx
    cA
    cA
    cfin4
    pwexr
    @0
    cA
    wceq
    @1
    @4
    cfin4
    @0
    cA
    pweq
    eleq1d
    elab3
    bitri
end
