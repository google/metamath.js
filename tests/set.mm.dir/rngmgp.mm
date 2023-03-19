include "crng.mm"
include "wcel.mm"
include "cabl.mm"
include "csgrp.mm"
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
include "isrng.mm"
include "simp2bi.mm"

theorem rngmgp
  let cR: class R
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume rngmgp.g: |- G = ( mulGrp ` R )


  assert |- ( R e. Rng -> G e. SGrp )

  proof
    cR
    crng
    wcel
    cR
    cabl
    wcel
    cG
    csgrp
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
    rngmgp.g
    @3
    eqid
    @4
    eqid
    isrng
    simp2bi
end
