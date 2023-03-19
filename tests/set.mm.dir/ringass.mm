include "crg.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmnd.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "ringmgp.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "mndass.mm"
include "sylan.mm"

theorem ringass
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  assume ringcl.b: |- B = ( Base ` R )
  assume ringcl.t: |- .x. = ( .r ` R )


  assert |- ( ( R e. Ring /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .x. Y ) .x. Z ) = ( X .x. ( Y .x. Z ) ) )

  proof
    cR
    crg
    wcel
    cR
    cmgp
    cfv
    #
    cmnd
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    cZ
    cB
    wcel
    w3a
    cX
    cY
    c.x
    co
    cZ
    c.x
    co
    cX
    cY
    cZ
    c.x
    co
    c.x
    co
    wceq
    cR
    @0
    @0
    eqid
    #
    ringmgp
    cB
    c.x
    @0
    cX
    cY
    cZ
    cB
    cR
    @0
    @1
    ringcl.b
    mgpbas
    cR
    c.x
    @0
    @1
    ringcl.t
    mgpplusg
    mndass
    sylan
end
