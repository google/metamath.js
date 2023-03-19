include "cgrp.mm"
include "wcel.mm"
include "csn.mm"
include "csubg.mm"
include "cfv.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "csg.mm"
include "wral.mm"
include "cbs.mm"
include "cnsg.mm"
include "0subg.mm"
include "wa.mm"
include "wceq.mm"
include "elsni.mm"
include "ad2antll.mm"
include "oveq2d.mm"
include "eqid.mm"
include "grprid.mm"
include "adantrr.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "grpsubid.mm"
include "ovex.mm"
include "elsn.mm"
include "sylibr.mm"
include "ralrimivva.mm"
include "isnsg3.mm"
include "sylanbrc.mm"

theorem 0nsg
  let cG: class G
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume 0nsg.z: |- .0. = ( 0g ` G )


  assert |- ( G e. Grp -> { .0. } e. ( NrmSGrp ` G ) )

  proof
    cG
    cgrp
    wcel
    #
    c.0
    csn
    #
    cG
    csubg
    cfv
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @2
    cG
    csg
    cfv
    #
    co
    #
    @1
    wcel
    #
    vy
    @1
    wral
    vx
    cG
    cbs
    cfv
    #
    wral
    @1
    cG
    cnsg
    cfv
    wcel
    cG
    c.0
    0nsg.z
    0subg
    @0
    @8
    vx
    vy
    @9
    @1
    @0
    @2
    @9
    wcel
    #
    @3
    @1
    wcel
    #
    wa
    wa
    #
    @7
    c.0
    wceq
    @8
    @12
    @7
    @2
    @2
    @6
    co
    #
    c.0
    @12
    @5
    @2
    @2
    @6
    @12
    @5
    @2
    c.0
    @4
    co
    #
    @2
    @12
    @3
    c.0
    @2
    @4
    @11
    @3
    c.0
    wceq
    @0
    @10
    @3
    c.0
    elsni
    ad2antll
    oveq2d
    @0
    @10
    @14
    @2
    wceq
    @11
    @9
    @4
    cG
    @2
    c.0
    @9
    eqid
    #
    @4
    eqid
    #
    0nsg.z
    grprid
    adantrr
    eqtrd
    oveq1d
    @0
    @10
    @13
    c.0
    wceq
    @11
    @9
    cG
    @6
    @2
    c.0
    @15
    0nsg.z
    @6
    eqid
    #
    grpsubid
    adantrr
    eqtrd
    @7
    c.0
    @5
    @2
    @6
    ovex
    elsn
    sylibr
    ralrimivva
    vx
    vy
    @4
    @1
    cG
    @6
    @9
    @15
    @16
    @17
    isnsg3
    sylanbrc
end
