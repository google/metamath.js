include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cur.mm"
include "cfv.mm"
include "cmulr.mm"
include "co.mm"
include "wbr.mm"
include "id.mm"
include "eqid.mm"
include "ringidcl.mm"
include "dvdsrmul.mm"
include "syl2anr.mm"
include "ringlidm.mm"
include "breqtrd.mm"

theorem dvdsrid
  let cB: class B
  let c.pa: class .||
  let cR: class R
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


  assert |- ( ( R e. Ring /\ X e. B ) -> X .|| X )

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
    cX
    cR
    cur
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
    c.pa
    @1
    @1
    @2
    cB
    wcel
    cX
    @4
    c.pa
    wbr
    @0
    @1
    id
    cB
    cR
    @2
    dvdsr.1
    @2
    eqid
    #
    ringidcl
    cB
    c.pa
    cR
    @3
    cX
    @2
    dvdsr.1
    dvdsr.2
    @3
    eqid
    #
    dvdsrmul
    syl2anr
    cB
    cR
    @3
    @2
    cX
    dvdsr.1
    @6
    @5
    ringlidm
    breqtrd
end
