include "crg.mm"
include "wcel.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "1unit.mm"
include "cbs.mm"
include "wss.mm"
include "eqid.mm"
include "unitss.mm"
include "ringidss.mm"
include "mp3an2.mm"
include "mpdan.mm"

theorem unitgrpid
  let cR: class R
  let cU: class U
  let c.1: class .1.
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  assume unitmulcl.1: |- U = ( Unit ` R )
  assume unitgrp.2: |- G = ( ( mulGrp ` R ) |`s U )
  assume unitgrp.3: |- .1. = ( 1r ` R )


  assert |- ( R e. Ring -> .1. = ( 0g ` G ) )

  proof
    cR
    crg
    wcel
    #
    c.1
    cU
    wcel
    #
    c.1
    cG
    c0g
    cfv
    wceq
    #
    cR
    cU
    c.1
    unitmulcl.1
    unitgrp.3
    1unit
    @0
    cU
    cR
    cbs
    cfv
    #
    wss
    @1
    @2
    @3
    cR
    cU
    @3
    eqid
    #
    unitmulcl.1
    unitss
    cU
    @3
    cR
    c.1
    cG
    unitgrp.2
    @4
    unitgrp.3
    ringidss
    mp3an2
    mpdan
end
