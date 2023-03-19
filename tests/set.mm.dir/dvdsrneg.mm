include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cur.mm"
include "cfv.mm"
include "cmulr.mm"
include "co.mm"
include "wbr.mm"
include "id.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "eqid.mm"
include "ringidcl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "dvdsrmul.mm"
include "syl2anr.mm"
include "simpl.mm"
include "simpr.mm"
include "ringnegl.mm"
include "breqtrd.mm"

theorem dvdsrneg
  let cB: class B
  let c.pa: class .||
  let cR: class R
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  let vz: setvar z
  let cY: class Y
  let cZ: class Z
  let c.x: class .x.
  assume dvdsr.1: |- B = ( Base ` R )
  assume dvdsr.2: |- .|| = ( ||r ` R )
  assume dvdsrneg.5: |- N = ( invg ` R )


  assert |- ( ( R e. Ring /\ X e. B ) -> X .|| ( N ` X ) )

  proof
    cR
    crg
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    cR
    cur
    cfv
    #
    cN
    cfv
    #
    cX
    cR
    cmulr
    cfv
    #
    co
    #
    cX
    cN
    cfv
    c.pa
    @1
    @1
    @4
    cB
    wcel
    #
    cX
    @6
    c.pa
    wbr
    @0
    @1
    id
    @0
    cR
    cgrp
    wcel
    @3
    cB
    wcel
    @7
    cR
    ringgrp
    cB
    cR
    @3
    dvdsr.1
    @3
    eqid
    #
    ringidcl
    cB
    cR
    cN
    @3
    dvdsr.1
    dvdsrneg.5
    grpinvcl
    syl2anc
    cB
    c.pa
    cR
    @5
    cX
    @4
    dvdsr.1
    dvdsr.2
    @5
    eqid
    #
    dvdsrmul
    syl2anr
    @2
    cB
    cR
    @5
    @3
    cN
    cX
    dvdsr.1
    @9
    @8
    dvdsrneg.5
    @0
    @1
    simpl
    @0
    @1
    simpr
    ringnegl
    breqtrd
end
