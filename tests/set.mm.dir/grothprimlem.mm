include "cv.mm"
include "cpr.mm"
include "wcel.mm"
include "weq.mm"
include "wo.mm"
include "cab.mm"
include "wel.mm"
include "wb.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "dfpr2.mm"
include "eleq1i.mm"
include "clabel.mm"
include "bitri.mm"

theorem grothprimlem
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t

  disjoint v w
  disjoint u w
  disjoint h w
  disjoint g w
  disjoint u v
  disjoint h v
  disjoint g v
  disjoint h u
  disjoint g u
  disjoint g h
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint t x
  disjoint h x
  disjoint g x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint t y
  disjoint h y
  disjoint g y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint t z
  disjoint h z
  disjoint g z
  disjoint t w
  disjoint t v
  disjoint t u
  disjoint h t
  disjoint g t
  assert |- ( { u , v } e. w <-> E. g ( g e. w /\ A. h ( h e. g <-> ( h = u \/ h = v ) ) ) )

  proof
    vu
    cv
    #
    vv
    cv
    #
    cpr
    #
    vw
    cv
    #
    wcel
    vh
    vu
    weq
    vh
    vv
    weq
    wo
    #
    vh
    cab
    #
    @3
    wcel
    vg
    vw
    wel
    vh
    vg
    wel
    @4
    wb
    vh
    wal
    wa
    vg
    wex
    @2
    @5
    @3
    vh
    @0
    @1
    dfpr2
    eleq1i
    @4
    vh
    vg
    @3
    clabel
    bitri
end
