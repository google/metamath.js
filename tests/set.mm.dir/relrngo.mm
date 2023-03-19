include "cv.mm"
include "cablo.mm"
include "wcel.mm"
include "crn.mm"
include "cxp.mm"
include "wf.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "wral.mm"
include "wrex.mm"
include "crngo.mm"
include "df-rngo.mm"
include "relopabi.mm"

theorem relrngo
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- Rel RingOps

  proof
    vg
    cv
    #
    cablo
    wcel
    @0
    crn
    #
    @1
    cxp
    @1
    vh
    cv
    #
    wf
    wa
    vx
    cv
    #
    vy
    cv
    #
    @2
    co
    #
    vz
    cv
    #
    @2
    co
    @3
    @4
    @6
    @2
    co
    #
    @2
    co
    wceq
    @3
    @4
    @6
    @0
    co
    @2
    co
    @5
    @3
    @6
    @2
    co
    #
    @0
    co
    wceq
    @3
    @4
    @0
    co
    @6
    @2
    co
    @8
    @7
    @0
    co
    wceq
    w3a
    vz
    @1
    wral
    vy
    @1
    wral
    vx
    @1
    wral
    @5
    @4
    wceq
    @4
    @3
    @2
    co
    @4
    wceq
    wa
    vy
    @1
    wral
    vx
    @1
    wrex
    wa
    wa
    vg
    vh
    crngo
    vx
    vy
    vz
    vg
    vh
    df-rngo
    relopabi
end
