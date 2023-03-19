include "crngo.mm"
include "wcel.mm"
include "cablo.mm"
include "crn.mm"
include "cxp.mm"
include "c2nd.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "eqid.mm"
include "rngoi.mm"
include "simplld.mm"

theorem rngoablo
  let cR: class R
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ringabl.1: |- G = ( 1st ` R )


  assert |- ( R e. RingOps -> G e. AbelOp )

  proof
    cR
    crngo
    wcel
    cG
    cablo
    wcel
    cG
    crn
    #
    @0
    cxp
    @0
    cR
    c2nd
    cfv
    #
    wf
    vx
    cv
    #
    vy
    cv
    #
    @1
    co
    #
    vz
    cv
    #
    @1
    co
    @2
    @3
    @5
    @1
    co
    #
    @1
    co
    wceq
    @2
    @3
    @5
    cG
    co
    @1
    co
    @4
    @2
    @5
    @1
    co
    #
    cG
    co
    wceq
    @2
    @3
    cG
    co
    @5
    @1
    co
    @7
    @6
    cG
    co
    wceq
    w3a
    vz
    @0
    wral
    vy
    @0
    wral
    vx
    @0
    wral
    @4
    @3
    wceq
    @3
    @2
    @1
    co
    @3
    wceq
    wa
    vy
    @0
    wral
    vx
    @0
    wrex
    wa
    vx
    vy
    vz
    cR
    cG
    @1
    @0
    ringabl.1
    @1
    eqid
    @0
    eqid
    rngoi
    simplld
end
