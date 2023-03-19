include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "com.mm"
include "wrex.mm"
include "cab.mm"
include "cfn.mm"
include "cima.mm"
include "ensymb.mm"
include "rexbii.mm"
include "abbii.mm"
include "df-fin.mm"
include "dfima2.mm"
include "3eqtr4i.mm"

theorem dffin1-5
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- Fin = ( ~~ " _om )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cen
    wbr
    #
    vy
    com
    wrex
    #
    vx
    cab
    @1
    @0
    cen
    wbr
    #
    vy
    com
    wrex
    #
    vx
    cab
    cfn
    cen
    com
    cima
    @3
    @5
    vx
    @2
    @4
    vy
    com
    @0
    @1
    ensymb
    rexbii
    abbii
    vx
    vy
    df-fin
    vy
    vx
    cen
    com
    dfima2
    3eqtr4i
end
