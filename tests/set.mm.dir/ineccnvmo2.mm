include "cv.mm"
include "wceq.mm"
include "ccnv.mm"
include "cec.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "crn.mm"
include "wral.mm"
include "wbr.mm"
include "wrmo.mm"
include "wal.mm"
include "wmo.mm"
include "ineccnvmo.mm"
include "alrmomorn.mm"
include "bitri.mm"

theorem ineccnvmo2
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cF: class F

  disjoint F u
  disjoint F x
  disjoint F y
  disjoint u x
  disjoint u y
  disjoint x y
  assert |- ( A. x e. ran F A. y e. ran F ( x = y \/ ( [ x ] `' F i^i [ y ] `' F ) = (/) ) <-> A. u E* x u F x )

  proof
    vx
    cv
    #
    vy
    cv
    #
    wceq
    @0
    cF
    ccnv
    #
    cec
    @1
    @2
    cec
    cin
    c0
    wceq
    wo
    vy
    cF
    crn
    #
    wral
    vx
    @3
    wral
    vu
    cv
    @0
    cF
    wbr
    #
    vx
    @3
    wrmo
    vu
    wal
    @4
    vx
    wmo
    vu
    wal
    vu
    vx
    vy
    @3
    cF
    ineccnvmo
    vu
    vx
    cF
    alrmomorn
    bitri
end
