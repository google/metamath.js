include "cvv.mm"
include "wcel.mm"
include "crab.mm"
include "rabexg.mm"
include "wn.mm"
include "c0.mm"
include "wrex.mm"
include "wceq.mm"
include "cv.mm"
include "simpl.mm"
include "nrexdv.mm"
include "rabn0.mm"
include "necon1bbii.mm"
include "sylib.mm"
include "0ex.mm"
include "syl6eqel.mm"
include "pm2.61i.mm"

theorem class2set
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- { x e. A | A e. _V } e. _V

  proof
    cA
    cvv
    wcel
    #
    @0
    vx
    cA
    crab
    #
    cvv
    wcel
    @0
    vx
    cA
    cvv
    rabexg
    @0
    wn
    #
    @1
    c0
    cvv
    @2
    @0
    vx
    cA
    wrex
    #
    wn
    @1
    c0
    wceq
    @2
    @0
    vx
    cA
    @2
    vx
    cv
    cA
    wcel
    simpl
    nrexdv
    @3
    @1
    c0
    @0
    vx
    cA
    rabn0
    necon1bbii
    sylib
    0ex
    syl6eqel
    pm2.61i
end
