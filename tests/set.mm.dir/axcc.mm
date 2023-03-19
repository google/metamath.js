include "cv.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "com.mm"
include "cuni.mm"
include "cfv.mm"
include "cmpt2.mm"
include "ccnv.mm"
include "csuc.mm"
include "cmpt.mm"
include "eqid.mm"
include "axcclem.mm"

theorem axcc
  let vx: setvar x
  let vz: setvar z
  let vf: setvar f
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y

  disjoint f x
  disjoint f z
  disjoint x z
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f y
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint y z
  assert |- ( x ~~ _om -> E. f A. z e. x ( z =/= (/) -> ( f ` z ) e. z ) )

  proof
    vx
    vy
    vz
    vw
    vx
    cv
    c0
    csn
    cdif
    #
    vv
    vf
    vu
    vt
    vt
    vy
    com
    @0
    cuni
    vt
    cv
    vv
    cv
    #
    cfv
    cmpt2
    #
    vw
    @0
    vw
    cv
    @1
    ccnv
    cfv
    csuc
    vu
    cv
    cfv
    cmpt
    #
    @0
    eqid
    @2
    eqid
    @3
    eqid
    axcclem
end
