include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "w3a.mm"
include "csn.mm"
include "cdif.mm"
include "wa.mm"
include "cv.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "clogb.mm"
include "cvv.mm"
include "cpr.mm"
include "df-logb.mm"
include "ovexd.mm"
include "ralrimivva.mm"
include "cnex.mm"
include "difexg.mm"
include "mp1i.mm"
include "eldifpr.mm"
include "biimpri.mm"
include "adantr.mm"
include "simpr.mm"
include "fvmpt2curryd.mm"

theorem logbfval
  let cB: class B
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( B e. CC /\ B =/= 0 /\ B =/= 1 ) /\ X e. ( CC \ { 0 } ) ) -> ( ( curry logb ` B ) ` X ) = ( B logb X ) )

  proof
    cB
    cc
    wcel
    cB
    cc0
    wne
    cB
    c1
    wne
    w3a
    #
    cX
    cc
    cc0
    csn
    #
    cdif
    #
    wcel
    #
    wa
    #
    vx
    vy
    cB
    cX
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
    #
    clogb
    cvv
    cvv
    cc
    cc0
    c1
    cpr
    cdif
    #
    @2
    vx
    vy
    df-logb
    @4
    @9
    cvv
    wcel
    vx
    vy
    @10
    @2
    @4
    @7
    @10
    wcel
    @5
    @2
    wcel
    wa
    wa
    @6
    @8
    cdiv
    ovexd
    ralrimivva
    cc
    cvv
    wcel
    @2
    cvv
    wcel
    @4
    cnex
    cc
    @1
    cvv
    difexg
    mp1i
    @0
    cB
    @10
    wcel
    #
    @3
    @11
    @0
    cB
    cc
    cc0
    c1
    eldifpr
    biimpri
    adantr
    @0
    @3
    simpr
    fvmpt2curryd
end
