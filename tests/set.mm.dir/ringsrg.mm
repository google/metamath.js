include "crg.mm"
include "wcel.mm"
include "ccmn.mm"
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
include "c0g.mm"
include "csrg.mm"
include "ringcmn.mm"
include "eqid.mm"
include "ringmgp.mm"
include "cgrp.mm"
include "isring.mm"
include "simp3bi.mm"
include "ringlz.mm"
include "ringrz.mm"
include "jca.mm"
include "ralrimiva.mm"
include "r19.26.mm"
include "sylanbrc.mm"
include "issrg.mm"
include "syl3anbrc.mm"

theorem ringsrg
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( R e. Ring -> R e. SRing )

  proof
    cR
    crg
    wcel
    #
    cR
    ccmn
    wcel
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
    @3
    @4
    @7
    co
    @3
    @5
    @7
    co
    #
    @6
    co
    wceq
    @3
    @4
    @6
    co
    @5
    @7
    co
    @8
    @4
    @5
    @7
    co
    @6
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
    @9
    wral
    #
    cR
    c0g
    cfv
    #
    @3
    @7
    co
    @11
    wceq
    #
    @3
    @11
    @7
    co
    @11
    wceq
    #
    wa
    #
    wa
    vx
    @9
    wral
    #
    cR
    csrg
    wcel
    cR
    ringcmn
    cR
    @1
    @1
    eqid
    #
    ringmgp
    @0
    @10
    vx
    @9
    wral
    #
    @14
    vx
    @9
    wral
    @15
    @0
    cR
    cgrp
    wcel
    @2
    @17
    vx
    vy
    vz
    @9
    @6
    cR
    @7
    @1
    @9
    eqid
    #
    @16
    @6
    eqid
    #
    @7
    eqid
    #
    isring
    simp3bi
    @0
    @14
    vx
    @9
    @0
    @3
    @9
    wcel
    wa
    @12
    @13
    @9
    cR
    @7
    @3
    @11
    @18
    @20
    @11
    eqid
    #
    ringlz
    @9
    cR
    @7
    @3
    @11
    @18
    @20
    @21
    ringrz
    jca
    ralrimiva
    @10
    @14
    vx
    @9
    r19.26
    sylanbrc
    vx
    vy
    vz
    @9
    @6
    cR
    @7
    @1
    @11
    @18
    @16
    @19
    @20
    @21
    issrg
    syl3anbrc
end
