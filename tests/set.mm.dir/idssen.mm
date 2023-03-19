include "cid.mm"
include "cen.mm"
include "reli.mm"
include "cv.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "weq.mm"
include "vex.mm"
include "ideq.mm"
include "cvv.mm"
include "wi.mm"
include "eqeng.mm"
include "ax-mp.mm"
include "sylbi.mm"
include "df-br.mm"
include "3imtr3i.mm"
include "relssi.mm"

theorem idssen
  let vx: setvar x
  let vy: setvar y


  assert |- _I C_ ~~

  proof
    vx
    vy
    cid
    cen
    reli
    vx
    cv
    #
    vy
    cv
    #
    cid
    wbr
    #
    @0
    @1
    cen
    wbr
    #
    @0
    @1
    cop
    #
    cid
    wcel
    @4
    cen
    wcel
    @2
    vx
    vy
    weq
    #
    @3
    @0
    @1
    vy
    vex
    ideq
    @0
    cvv
    wcel
    @5
    @3
    wi
    vx
    vex
    @0
    @1
    cvv
    eqeng
    ax-mp
    sylbi
    @0
    @1
    cid
    df-br
    @0
    @1
    cen
    df-br
    3imtr3i
    relssi
end
