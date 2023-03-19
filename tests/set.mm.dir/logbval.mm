include "cc.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cdif.mm"
include "csn.mm"
include "cv.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "clogb.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "df-logb.mm"
include "ovex.mm"
include "ovmpt2.mm"

theorem logbval
  let cB: class B
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( B e. ( CC \ { 0 , 1 } ) /\ X e. ( CC \ { 0 } ) ) -> ( B logb X ) = ( ( log ` X ) / ( log ` B ) ) )

  proof
    vx
    vy
    cB
    cX
    cc
    cc0
    c1
    cpr
    cdif
    cc
    cc0
    csn
    cdif
    vy
    cv
    #
    clog
    cfv
    #
    vx
    cv
    #
    clog
    cfv
    #
    cdiv
    co
    cX
    clog
    cfv
    #
    cB
    clog
    cfv
    #
    cdiv
    co
    clogb
    @1
    @5
    cdiv
    co
    @2
    cB
    wceq
    @3
    @5
    @1
    cdiv
    @2
    cB
    clog
    fveq2
    oveq2d
    @0
    cX
    wceq
    @1
    @4
    @5
    cdiv
    @0
    cX
    clog
    fveq2
    oveq1d
    vx
    vy
    df-logb
    @4
    @5
    cdiv
    ovex
    ovmpt2
end
