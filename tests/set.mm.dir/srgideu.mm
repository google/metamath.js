include "csrg.mm"
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
include "srgmgp.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "mndideu.mm"
include "syl.mm"

theorem srgideu
  let vx: setvar x
  let vu: setvar u
  let cB: class B
  let cR: class R
  let c.x: class .x.
  assume srgcl.b: |- B = ( Base ` R )
  assume srgcl.t: |- .x. = ( .r ` R )

  disjoint u x
  disjoint B u
  disjoint B x
  disjoint R u
  disjoint R x
  disjoint .x. u
  disjoint .x. x
  assert |- ( R e. SRing -> E! u e. B A. x e. B ( ( u .x. x ) = x /\ ( x .x. u ) = x ) )

  proof
    cR
    csrg
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
    srgmgp
    vx
    vu
    cB
    c.x
    @0
    cB
    cR
    @0
    @3
    srgcl.b
    mgpbas
    cR
    c.x
    @0
    @3
    srgcl.t
    mgpplusg
    mndideu
    syl
end
