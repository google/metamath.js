include "cwina.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "ccf.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "csdm.mm"
include "wbr.mm"
include "wrex.mm"
include "wral.mm"
include "w3a.mm"
include "ccrd.mm"
include "elwina.mm"
include "cardcf.mm"
include "fveq2.mm"
include "id.mm"
include "3eqtr3a.mm"
include "3ad2ant2.mm"
include "sylbi.mm"

theorem winacard
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. InaccW -> ( card ` A ) = A )

  proof
    cA
    cwina
    wcel
    cA
    c0
    wne
    #
    cA
    ccf
    cfv
    #
    cA
    wceq
    #
    vx
    cv
    vy
    cv
    csdm
    wbr
    vy
    cA
    wrex
    vx
    cA
    wral
    #
    w3a
    cA
    ccrd
    cfv
    #
    cA
    wceq
    #
    vx
    vy
    cA
    elwina
    @2
    @0
    @5
    @3
    @2
    @1
    ccrd
    cfv
    @1
    @4
    cA
    cA
    cardcf
    @1
    cA
    ccrd
    fveq2
    @2
    id
    3eqtr3a
    3ad2ant2
    sylbi
end
