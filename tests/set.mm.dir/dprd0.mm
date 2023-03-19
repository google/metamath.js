include "cgrp.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cmpt.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cvv.mm"
include "0ex.mm"
include "dprdz.mm"
include "mpan2.mm"
include "mpt0.mm"
include "breq2i.mm"
include "oveq2i.mm"
include "eqeq1i.mm"
include "anbi12i.mm"
include "sylib.mm"

theorem dprd0
  let cG: class G
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cI: class I
  let cV: class V
  assume dprd0.0: |- .0. = ( 0g ` G )


  assert |- ( G e. Grp -> ( G dom DProd (/) /\ ( G DProd (/) ) = { .0. } ) )

  proof
    cG
    cgrp
    wcel
    #
    cG
    vx
    c0
    c.0
    csn
    #
    cmpt
    #
    cdprd
    cdm
    #
    wbr
    #
    cG
    @2
    cdprd
    co
    #
    @1
    wceq
    #
    wa
    #
    cG
    c0
    @3
    wbr
    #
    cG
    c0
    cdprd
    co
    #
    @1
    wceq
    #
    wa
    @0
    c0
    cvv
    wcel
    @7
    0ex
    vx
    cG
    c0
    cvv
    c.0
    dprd0.0
    dprdz
    mpan2
    @4
    @8
    @6
    @10
    @2
    c0
    cG
    @3
    vx
    @1
    mpt0
    #
    breq2i
    @5
    @9
    @1
    @2
    c0
    cG
    cdprd
    @11
    oveq2i
    eqeq1i
    anbi12i
    sylib
end
