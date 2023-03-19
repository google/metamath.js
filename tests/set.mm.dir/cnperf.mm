include "cc.mm"
include "crest.mm"
include "co.mm"
include "cperf.mm"
include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "cv.mm"
include "cr.mm"
include "caddc.mm"
include "recn.mm"
include "addcl.mm"
include "sylan2.mm"
include "ssid.mm"
include "reperflem.mm"
include "eqeltrri.mm"

theorem cnperf
  let cJ: class J
  let vn: setvar n
  let vr: setvar r
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let cS: class S
  assume recld2.1: |- J = ( TopOpen ` CCfld )


  assert |- J e. Perf

  proof
    cJ
    cc
    crest
    co
    #
    cJ
    cperf
    cJ
    cc
    ctopon
    cfv
    #
    wcel
    @0
    cJ
    wceq
    cJ
    recld2.1
    cnfldtopon
    #
    cJ
    @1
    cc
    cc
    cJ
    @2
    toponunii
    restid
    ax-mp
    vy
    vx
    cc
    cJ
    recld2.1
    vy
    cv
    #
    cr
    wcel
    vx
    cv
    #
    cc
    wcel
    @3
    cc
    wcel
    @4
    @3
    caddc
    co
    cc
    wcel
    @3
    recn
    @4
    @3
    addcl
    sylan2
    cc
    ssid
    reperflem
    eqeltrri
end
