include "crg.mm"
include "wcel.mm"
include "c0.mm"
include "cmdat.mm"
include "co.mm"
include "cfv.mm"
include "cur.mm"
include "cop.mm"
include "csn.mm"
include "mdet0pr.mm"
include "fveq1d.mm"
include "0ex.mm"
include "fvex.mm"
include "fvsn.mm"
include "syl6eq.mm"

theorem mdet0fv0
  let cR: class R
  let vm: setvar m
  let vp: setvar p
  let vx: setvar x


  assert |- ( R e. Ring -> ( ( (/) maDet R ) ` (/) ) = ( 1r ` R ) )

  proof
    cR
    crg
    wcel
    #
    c0
    c0
    cR
    cmdat
    co
    #
    cfv
    c0
    c0
    cR
    cur
    cfv
    #
    cop
    csn
    #
    cfv
    @2
    @0
    c0
    @1
    @3
    cR
    mdet0pr
    fveq1d
    c0
    @2
    0ex
    cR
    cur
    fvex
    fvsn
    syl6eq
end
