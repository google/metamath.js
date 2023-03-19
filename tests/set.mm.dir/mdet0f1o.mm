include "crg.mm"
include "wcel.mm"
include "c0.mm"
include "cmdat.mm"
include "co.mm"
include "cur.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "wceq.mm"
include "wf1o.mm"
include "mdet0pr.mm"
include "0ex.mm"
include "fvex.mm"
include "f1osn.mm"
include "f1oeq1.mm"
include "mpbiri.mm"
include "syl.mm"

theorem mdet0f1o
  let cR: class R
  let vm: setvar m
  let vp: setvar p
  let vx: setvar x


  assert |- ( R e. Ring -> ( (/) maDet R ) : { (/) } -1-1-onto-> { ( 1r ` R ) } )

  proof
    cR
    crg
    wcel
    c0
    cR
    cmdat
    co
    #
    c0
    cR
    cur
    cfv
    #
    cop
    csn
    #
    wceq
    #
    c0
    csn
    #
    @1
    csn
    #
    @0
    wf1o
    #
    cR
    mdet0pr
    @3
    @6
    @4
    @5
    @2
    wf1o
    c0
    @1
    0ex
    cR
    cur
    fvex
    f1osn
    @4
    @5
    @0
    @2
    f1oeq1
    mpbiri
    syl
end
