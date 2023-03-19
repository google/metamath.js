include "cgrp.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "csg.mm"
include "wral.mm"
include "cnsg.mm"
include "subgid.mm"
include "w3a.mm"
include "simp1.mm"
include "eqid.mm"
include "grpcl.mm"
include "simp2.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "isnsg3.mm"
include "sylanbrc.mm"

theorem nsgid
  let cB: class B
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  assume nsgid.z: |- B = ( Base ` G )


  assert |- ( G e. Grp -> B e. ( NrmSGrp ` G ) )

  proof
    cG
    cgrp
    wcel
    #
    cB
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
    @1
    cG
    csg
    cfv
    #
    co
    cB
    wcel
    #
    vy
    cB
    wral
    vx
    cB
    wral
    cB
    cG
    cnsg
    cfv
    wcel
    cB
    cG
    nsgid.z
    subgid
    @0
    @6
    vx
    vy
    cB
    cB
    @0
    @1
    cB
    wcel
    #
    @2
    cB
    wcel
    #
    @6
    @0
    @7
    @8
    w3a
    @0
    @4
    cB
    wcel
    @7
    @6
    @0
    @7
    @8
    simp1
    cB
    @3
    cG
    @1
    @2
    nsgid.z
    @3
    eqid
    #
    grpcl
    @0
    @7
    @8
    simp2
    cB
    cG
    @5
    @4
    @1
    nsgid.z
    @5
    eqid
    #
    grpsubcl
    syl3anc
    3expb
    ralrimivva
    vx
    vy
    @3
    cB
    cG
    @5
    cB
    nsgid.z
    @9
    @10
    isnsg3
    sylanbrc
end
