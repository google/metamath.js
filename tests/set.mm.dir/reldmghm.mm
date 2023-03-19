include "cgrp.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wsbc.mm"
include "cab.mm"
include "cghm.mm"
include "df-ghm.mm"
include "reldmmpt2.mm"

theorem reldmghm
  let vg: setvar g
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y


  assert |- Rel dom GrpHom

  proof
    vs
    vt
    cgrp
    cgrp
    vw
    cv
    #
    vt
    cv
    #
    cbs
    cfv
    vg
    cv
    #
    wf
    vx
    cv
    #
    vy
    cv
    #
    vs
    cv
    #
    cplusg
    cfv
    co
    @2
    cfv
    @3
    @2
    cfv
    @4
    @2
    cfv
    @1
    cplusg
    cfv
    co
    wceq
    vy
    @0
    wral
    vx
    @0
    wral
    wa
    vw
    @5
    cbs
    cfv
    wsbc
    vg
    cab
    cghm
    vx
    vy
    vw
    vt
    vg
    vs
    df-ghm
    reldmmpt2
end
