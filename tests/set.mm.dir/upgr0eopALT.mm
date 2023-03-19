include "wcel.mm"
include "cupgr.mm"
include "c0.mm"
include "cvv.mm"
include "cv.mm"
include "cvtx.mm"
include "cfv.mm"
include "wceq.mm"
include "ciedg.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "vex.mm"
include "a1i.mm"
include "simpr.mm"
include "upgr0e.mm"
include "ax-gen.mm"
include "id.mm"
include "0ex.mm"
include "gropeld.mm"

theorem upgr0eopALT
  let cV: class V
  let cW: class W
  let vg: setvar g


  assert |- ( V e. W -> <. V , (/) >. e. UPGraph )

  proof
    cV
    cW
    wcel
    #
    cupgr
    cW
    vg
    c0
    cV
    cvv
    vg
    cv
    #
    cvtx
    cfv
    cV
    wceq
    #
    @1
    ciedg
    cfv
    c0
    wceq
    #
    wa
    #
    @1
    cupgr
    wcel
    wi
    #
    vg
    wal
    @0
    @5
    vg
    @4
    @1
    cvv
    @1
    cvv
    wcel
    @4
    vg
    vex
    a1i
    @2
    @3
    simpr
    upgr0e
    ax-gen
    a1i
    @0
    id
    c0
    cvv
    wcel
    @0
    0ex
    a1i
    gropeld
end
