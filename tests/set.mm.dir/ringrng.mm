include "cabl.mm"
include "wcel.mm"
include "crg.mm"
include "crng.mm"
include "ringabl.mm"
include "cgrp.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmnd.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "cmulr.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "wral.mm"
include "w3a.mm"
include "eqid.mm"
include "isring.mm"
include "csgrp.mm"
include "simpl.mm"
include "mndsgrp.mm"
include "3ad2ant2.mm"
include "adantl.mm"
include "simpr3.mm"
include "isrng.mm"
include "syl3anbrc.mm"
include "ex.mm"
include "syl5bi.mm"
include "mpcom.mm"

theorem ringrng
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k


  assert |- ( R e. Ring -> R e. Rng )

  proof
    cR
    cabl
    wcel
    #
    cR
    crg
    wcel
    #
    cR
    crng
    wcel
    #
    cR
    ringabl
    @1
    cR
    cgrp
    wcel
    #
    cR
    cmgp
    cfv
    #
    cmnd
    wcel
    #
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
    @6
    @7
    @10
    co
    @6
    @8
    @10
    co
    #
    @9
    co
    wceq
    @6
    @7
    @9
    co
    @8
    @10
    co
    @11
    @7
    @8
    @10
    co
    @9
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
    @12
    wral
    vx
    @12
    wral
    #
    w3a
    #
    @0
    @2
    vx
    vy
    vz
    @12
    @9
    cR
    @10
    @4
    @12
    eqid
    #
    @4
    eqid
    #
    @9
    eqid
    #
    @10
    eqid
    #
    isring
    @0
    @14
    @2
    @0
    @14
    wa
    @0
    @4
    csgrp
    wcel
    #
    @13
    @2
    @0
    @14
    simpl
    @14
    @19
    @0
    @5
    @3
    @19
    @13
    @4
    mndsgrp
    3ad2ant2
    adantl
    @0
    @3
    @5
    @13
    simpr3
    vx
    vy
    vz
    @12
    @9
    cR
    @10
    @4
    @15
    @16
    @17
    @18
    isrng
    syl3anbrc
    ex
    syl5bi
    mpcom
end
