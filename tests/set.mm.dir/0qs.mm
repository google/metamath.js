include "c0.mm"
include "cqs.mm"
include "cv.mm"
include "cec.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "df-qs.mm"
include "rex0.mm"
include "abf.mm"
include "eqtri.mm"

theorem 0qs
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( (/) /. R ) = (/)

  proof
    c0
    cR
    cqs
    vy
    cv
    vx
    cv
    cR
    cec
    wceq
    #
    vx
    c0
    wrex
    #
    vy
    cab
    c0
    vx
    vy
    c0
    cR
    df-qs
    @1
    vy
    @0
    vx
    rex0
    abf
    eqtri
end
