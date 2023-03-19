include "crn.mm"
include "cv.mm"
include "cxp.mm"
include "vex.mm"
include "xpex.mm"
include "fnmpt2i.mm"

theorem dya2iocrfn
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cR: class R
  let vn: setvar n
  let cI: class I
  let cJ: class J
  assume sxbrsiga.0: |- J = ( topGen ` ran (,) )
  assume dya2ioc.1: |- I = ( x e. ZZ , n e. ZZ |-> ( ( x / ( 2 ^ n ) ) [,) ( ( x + 1 ) / ( 2 ^ n ) ) ) )
  assume dya2ioc.2: |- R = ( u e. ran I , v e. ran I |-> ( u X. v ) )

  disjoint n x
  disjoint I x
  disjoint u v
  disjoint I u
  disjoint I v
  assert |- R Fn ( ran I X. ran I )

  proof
    vu
    vv
    cI
    crn
    #
    @0
    vu
    cv
    #
    vv
    cv
    #
    cxp
    cR
    dya2ioc.2
    @1
    @2
    vu
    vex
    vv
    vex
    xpex
    fnmpt2i
end
