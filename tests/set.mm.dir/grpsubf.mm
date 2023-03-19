include "cgrp.mm"
include "wcel.mm"
include "cv.mm"
include "cminusg.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "cxp.mm"
include "wf.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "3adant2.mm"
include "grpcl.mm"
include "syld3an3.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "grpsubfval.mm"
include "fmpt2.mm"
include "sylib.mm"

theorem grpsubf
  let cB: class B
  let cG: class G
  let c.mi: class .-
  let vx: setvar x
  let vy: setvar y
  assume grpsubcl.b: |- B = ( Base ` G )
  assume grpsubcl.m: |- .- = ( -g ` G )


  assert |- ( G e. Grp -> .- : ( B X. B ) --> B )

  proof
    cG
    cgrp
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    cminusg
    cfv
    #
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    #
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
    cB
    cxp
    cB
    c.mi
    wf
    @0
    @7
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
    @7
    @0
    @8
    @9
    @4
    cB
    wcel
    #
    @7
    @0
    @9
    @10
    @8
    cB
    cG
    @3
    @2
    grpsubcl.b
    @3
    eqid
    #
    grpinvcl
    3adant2
    cB
    @5
    cG
    @1
    @4
    grpsubcl.b
    @5
    eqid
    #
    grpcl
    syld3an3
    3expb
    ralrimivva
    vx
    vy
    cB
    cB
    @6
    cB
    c.mi
    vx
    vy
    cB
    @5
    cG
    @3
    c.mi
    grpsubcl.b
    @12
    @11
    grpsubcl.m
    grpsubfval
    fmpt2
    sylib
end
