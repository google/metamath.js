include "cv.mm"
include "wcel.mm"
include "cab.mm"
include "cint.mm"
include "csn.mm"
include "cvv.mm"
include "wss.mm"
include "snex.mm"
include "eleq2.mm"
include "snid.mm"
include "intmin3.mm"
include "ax-mp.mm"
include "wi.mm"
include "elintab.mm"
include "id.mm"
include "mpgbir.mm"
include "snssi.mm"
include "eqssi.mm"

theorem intid
  let vx: setvar x
  let cA: class A
  assume intid.1: |- A e. _V

  disjoint A x
  assert |- |^| { x | A e. x } = { A }

  proof
    cA
    vx
    cv
    #
    wcel
    #
    vx
    cab
    cint
    #
    cA
    csn
    #
    @3
    cvv
    wcel
    @2
    @3
    wss
    cA
    snex
    @1
    cA
    @3
    wcel
    vx
    @3
    cvv
    @0
    @3
    cA
    eleq2
    cA
    intid.1
    snid
    intmin3
    ax-mp
    cA
    @2
    wcel
    #
    @3
    @2
    wss
    @4
    @1
    @1
    wi
    vx
    @1
    vx
    cA
    intid.1
    elintab
    @1
    id
    mpgbir
    cA
    @2
    snssi
    ax-mp
    eqssi
end
