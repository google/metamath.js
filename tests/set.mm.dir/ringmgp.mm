include "crg.mm"
include "wcel.mm"
include "cgrp.mm"
include "cmnd.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "cmulr.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "wral.mm"
include "eqid.mm"
include "isring.mm"
include "simp2bi.mm"

theorem ringmgp
  let cR: class R
  let cG: class G
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ringmgp.g: |- G = ( mulGrp ` R )


  assert |- ( R e. Ring -> G e. Mnd )

  proof
    cR
    crg
    wcel
    cR
    cgrp
    wcel
    cG
    cmnd
    wcel
    vx
    cv
    #
    vy
    cv
    #
    vz
    cv
    #
    cR
    cplusg
    cfv
    #
    co
    cR
    cmulr
    cfv
    #
    co
    @0
    @1
    @4
    co
    @0
    @2
    @4
    co
    #
    @3
    co
    wceq
    @0
    @1
    @3
    co
    @2
    @4
    co
    @5
    @1
    @2
    @4
    co
    @3
    co
    wceq
    wa
    vz
    cR
    cbs
    cfv
    #
    wral
    vy
    @6
    wral
    vx
    @6
    wral
    vx
    vy
    vz
    @6
    @3
    cR
    @4
    cG
    @6
    eqid
    ringmgp.g
    @3
    eqid
    @4
    eqid
    isring
    simp2bi
end
