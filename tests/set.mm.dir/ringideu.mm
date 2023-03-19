include "crg.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmnd.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wreu.mm"
include "eqid.mm"
include "ringmgp.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "mndideu.mm"
include "syl.mm"

theorem ringideu
  let vx: setvar x
  let vu: setvar u
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let vy: setvar y
  assume ringcl.b: |- B = ( Base ` R )
  assume ringcl.t: |- .x. = ( .r ` R )

  disjoint B x
  disjoint R x
  disjoint u x
  disjoint B u
  disjoint R u
  disjoint .x. u
  disjoint .x. x
  disjoint x y
  disjoint B y
  disjoint R y
  assert |- ( R e. Ring -> E! u e. B A. x e. B ( ( u .x. x ) = x /\ ( x .x. u ) = x ) )

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
    vu
    cv
    #
    vx
    cv
    #
    c.x
    co
    @2
    wceq
    @2
    @1
    c.x
    co
    @2
    wceq
    wa
    vx
    cB
    wral
    vu
    cB
    wreu
    cR
    @0
    @0
    eqid
    #
    ringmgp
    vx
    vu
    cB
    c.x
    @0
    cB
    cR
    @0
    @3
    ringcl.b
    mgpbas
    cR
    c.x
    @0
    @3
    ringcl.t
    mgpplusg
    mndideu
    syl
end
