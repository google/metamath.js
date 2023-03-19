include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "eqid.mm"
include "unitss.mm"
include "cmgp.mm"
include "mgpbas.mm"
include "ressbas2.mm"
include "ax-mp.mm"

theorem unitgrpbas
  let cR: class R
  let cU: class U
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  assume unitmulcl.1: |- U = ( Unit ` R )
  assume unitgrp.2: |- G = ( ( mulGrp ` R ) |`s U )


  assert |- U = ( Base ` G )

  proof
    cU
    cR
    cbs
    cfv
    #
    wss
    cU
    cG
    cbs
    cfv
    wceq
    @0
    cR
    cU
    @0
    eqid
    #
    unitmulcl.1
    unitss
    cU
    @0
    cG
    cR
    cmgp
    cfv
    #
    unitgrp.2
    @0
    cR
    @2
    @2
    eqid
    @1
    mgpbas
    ressbas2
    ax-mp
end
