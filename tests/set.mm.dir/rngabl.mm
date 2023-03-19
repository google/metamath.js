include "crng.mm"
include "wcel.mm"
include "cabl.mm"
include "cmgp.mm"
include "cfv.mm"
include "csgrp.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "cmulr.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "wral.mm"
include "eqid.mm"
include "isrng.mm"
include "simp1bi.mm"

theorem rngabl
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k


  assert |- ( R e. Rng -> R e. Abel )

  proof
    cR
    crng
    wcel
    cR
    cabl
    wcel
    cR
    cmgp
    cfv
    #
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
    @1
    @2
    @5
    co
    @1
    @3
    @5
    co
    #
    @4
    co
    wceq
    @1
    @2
    @4
    co
    @3
    @5
    co
    @6
    @2
    @3
    @5
    co
    @4
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
    @7
    wral
    vx
    @7
    wral
    vx
    vy
    vz
    @7
    @4
    cR
    @5
    @0
    @7
    eqid
    @0
    eqid
    @4
    eqid
    @5
    eqid
    isrng
    simp1bi
end
