include "cgrp.mm"
include "wcel.mm"
include "c0.mm"
include "cvv.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cxp.mm"
include "wf.mm"
include "c0g.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "cplusg.mm"
include "wral.mm"
include "cga.mm"
include "0ex.mm"
include "jctr.mm"
include "f0.mm"
include "xp0.mm"
include "feq2i.mm"
include "mpbir.mm"
include "ral0.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "eqid.mm"
include "isga.mm"
include "sylanbrc.mm"

theorem ga0
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( G e. Grp -> (/) e. ( G GrpAct (/) ) )

  proof
    cG
    cgrp
    wcel
    #
    @0
    c0
    cvv
    wcel
    #
    wa
    cG
    cbs
    cfv
    #
    c0
    cxp
    #
    c0
    c0
    wf
    #
    cG
    c0g
    cfv
    #
    vx
    cv
    #
    c0
    co
    @6
    wceq
    vy
    cv
    #
    vz
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    @6
    c0
    co
    @7
    @8
    @6
    c0
    co
    c0
    co
    wceq
    vz
    @2
    wral
    vy
    @2
    wral
    wa
    #
    vx
    c0
    wral
    #
    wa
    #
    c0
    cG
    c0
    cga
    co
    wcel
    @0
    @1
    0ex
    jctr
    @12
    @0
    @4
    @11
    @4
    c0
    c0
    c0
    wf
    c0
    f0
    @3
    c0
    c0
    c0
    @2
    xp0
    feq2i
    mpbir
    @10
    vx
    ral0
    pm3.2i
    a1i
    vx
    vy
    vz
    @9
    c0
    cG
    @2
    c0
    @5
    @2
    eqid
    @9
    eqid
    @5
    eqid
    isga
    sylanbrc
end
