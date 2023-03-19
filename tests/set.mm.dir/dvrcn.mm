include "ctdrg.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cinvr.mm"
include "cmulr.mm"
include "co.mm"
include "cmpt2.mm"
include "crest.mm"
include "ctx.mm"
include "ccn.mm"
include "eqid.mm"
include "dvrfval.mm"
include "tdrgtrg.mm"
include "ctps.mm"
include "ctopon.mm"
include "tdrgtps.mm"
include "istps.mm"
include "sylib.mm"
include "wss.mm"
include "unitss.mm"
include "resttopon.mm"
include "sylancl.mm"
include "cnmpt1st.mm"
include "cnmpt2nd.mm"
include "invrcn.mm"
include "cnmpt21f.mm"
include "cnmpt2mulr.mm"
include "syl5eqel.mm"

theorem dvrcn
  let c.dv: class ./
  let cR: class R
  let cU: class U
  let cJ: class J
  let vx: setvar x
  let vy: setvar y
  assume dvrcn.j: |- J = ( TopOpen ` R )
  assume dvrcn.d: |- ./ = ( /r ` R )
  assume dvrcn.u: |- U = ( Unit ` R )


  assert |- ( R e. TopDRing -> ./ e. ( ( J tX ( J |`t U ) ) Cn J ) )

  proof
    cR
    ctdrg
    wcel
    #
    c.dv
    vx
    vy
    cR
    cbs
    cfv
    #
    cU
    vx
    cv
    #
    vy
    cv
    #
    cR
    cinvr
    cfv
    #
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    cmpt2
    cJ
    cJ
    cU
    crest
    co
    #
    ctx
    co
    cJ
    ccn
    co
    vx
    vy
    @1
    c.dv
    cR
    @6
    cU
    @4
    @1
    eqid
    #
    @6
    eqid
    #
    dvrcn.u
    @4
    eqid
    #
    dvrcn.d
    dvrfval
    @0
    vx
    vy
    @2
    @5
    cR
    @6
    cJ
    cJ
    @7
    @1
    cU
    dvrcn.j
    @9
    cR
    tdrgtrg
    @0
    cR
    ctps
    wcel
    cJ
    @1
    ctopon
    cfv
    wcel
    #
    cR
    tdrgtps
    @1
    cJ
    cR
    @8
    dvrcn.j
    istps
    sylib
    #
    @0
    @11
    cU
    @1
    wss
    @7
    cU
    ctopon
    cfv
    wcel
    @12
    @1
    cR
    cU
    @8
    dvrcn.u
    unitss
    cU
    cJ
    @1
    resttopon
    sylancl
    #
    @0
    vx
    vy
    cJ
    @7
    @1
    cU
    @12
    @13
    cnmpt1st
    @0
    vx
    vy
    @3
    @4
    cJ
    @7
    @7
    cJ
    @1
    cU
    @12
    @13
    @0
    vx
    vy
    cJ
    @7
    @1
    cU
    @12
    @13
    cnmpt2nd
    cR
    cU
    @4
    cJ
    dvrcn.j
    @10
    dvrcn.u
    invrcn
    cnmpt21f
    cnmpt2mulr
    syl5eqel
end
