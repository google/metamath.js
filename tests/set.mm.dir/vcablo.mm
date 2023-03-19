include "cvc.mm"
include "wcel.mm"
include "cablo.mm"
include "cc.mm"
include "crn.mm"
include "cxp.mm"
include "c2nd.mm"
include "cfv.mm"
include "wf.mm"
include "c1.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "caddc.mm"
include "cmul.mm"
include "wa.mm"
include "eqid.mm"
include "vciOLD.mm"
include "simp1d.mm"

theorem vcablo
  let cG: class G
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume vcabl.1: |- G = ( 1st ` W )


  assert |- ( W e. CVecOLD -> G e. AbelOp )

  proof
    cW
    cvc
    wcel
    cG
    cablo
    wcel
    cc
    cG
    crn
    #
    cxp
    @0
    cW
    c2nd
    cfv
    #
    wf
    c1
    vx
    cv
    #
    @1
    co
    @2
    wceq
    vy
    cv
    #
    @2
    vz
    cv
    #
    cG
    co
    @1
    co
    @3
    @2
    @1
    co
    #
    @3
    @4
    @1
    co
    cG
    co
    wceq
    vz
    @0
    wral
    @3
    @4
    caddc
    co
    @2
    @1
    co
    @5
    @4
    @2
    @1
    co
    #
    cG
    co
    wceq
    @3
    @4
    cmul
    co
    @2
    @1
    co
    @3
    @6
    @1
    co
    wceq
    wa
    vz
    cc
    wral
    wa
    vy
    cc
    wral
    wa
    vx
    @0
    wral
    vx
    vy
    vz
    @1
    cG
    cW
    @0
    vcabl.1
    @1
    eqid
    @0
    eqid
    vciOLD
    simp1d
end
