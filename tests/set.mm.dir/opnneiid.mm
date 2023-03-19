include "ctop.mm"
include "wcel.mm"
include "cnei.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "neii2.mm"
include "wceq.mm"
include "eqss.mm"
include "eleq1a.mm"
include "syl5bir.mm"
include "rexlimiv.mm"
include "syl.mm"
include "ex.mm"
include "ssid.mm"
include "opnneiss.mm"
include "3exp.mm"
include "mpii.mm"
include "impbid.mm"

theorem opnneiid
  let cJ: class J
  let cN: class N
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let cM: class M
  let cS: class S


  assert |- ( J e. Top -> ( N e. ( ( nei ` J ) ` N ) <-> N e. J ) )

  proof
    cJ
    ctop
    wcel
    #
    cN
    cN
    cJ
    cnei
    cfv
    cfv
    wcel
    #
    cN
    cJ
    wcel
    #
    @0
    @1
    @2
    @0
    @1
    wa
    cN
    vx
    cv
    #
    wss
    @3
    cN
    wss
    wa
    #
    vx
    cJ
    wrex
    @2
    cN
    vx
    cJ
    cN
    neii2
    @4
    @2
    vx
    cJ
    @4
    cN
    @3
    wceq
    @3
    cJ
    wcel
    @2
    cN
    @3
    eqss
    @3
    cJ
    cN
    eleq1a
    syl5bir
    rexlimiv
    syl
    ex
    @0
    @2
    cN
    cN
    wss
    #
    @1
    cN
    ssid
    @0
    @2
    @5
    @1
    cN
    cJ
    cN
    opnneiss
    3exp
    mpii
    impbid
end
