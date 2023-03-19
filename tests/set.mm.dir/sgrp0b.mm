include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "c0.mm"
include "cop.mm"
include "cplusg.mm"
include "cpr.mm"
include "csgrp.mm"
include "wcel.mm"
include "cmgm.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "mgm0b.mm"
include "ral0.mm"
include "cvv.mm"
include "0ex.mm"
include "eqid.mm"
include "grpbase.mm"
include "ax-mp.mm"
include "issgrp.mm"
include "mpbir2an.mm"

theorem sgrp0b
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- { <. ( Base ` ndx ) , (/) >. , <. ( +g ` ndx ) , O >. } e. SGrp

  proof
    cnx
    cbs
    cfv
    c0
    cop
    cnx
    cplusg
    cfv
    cO
    cop
    cpr
    #
    csgrp
    wcel
    @0
    cmgm
    wcel
    vx
    cv
    #
    vy
    cv
    #
    @0
    cplusg
    cfv
    #
    co
    vz
    cv
    #
    @3
    co
    @1
    @2
    @4
    @3
    co
    @3
    co
    wceq
    vz
    c0
    wral
    vy
    c0
    wral
    #
    vx
    c0
    wral
    cO
    mgm0b
    @5
    vx
    ral0
    vx
    vy
    vz
    c0
    @0
    @3
    c0
    cvv
    wcel
    c0
    @0
    cbs
    cfv
    wceq
    0ex
    c0
    cO
    @0
    cvv
    @0
    eqid
    grpbase
    ax-mp
    @3
    eqid
    issgrp
    mpbir2an
end
