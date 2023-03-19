include "crg.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "eqid.mm"
include "mgpbas.mm"
include "ringidval.mm"
include "mgpplusg.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wreu.mm"
include "wrex.mm"
include "ringideu.mm"
include "reurex.mm"
include "syl.mm"
include "ismgmid.mm"

theorem isringid
  let vx: setvar x
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let cI: class I
  let vy: setvar y
  assume rngidm.b: |- B = ( Base ` R )
  assume rngidm.t: |- .x. = ( .r ` R )
  assume rngidm.u: |- .1. = ( 1r ` R )

  disjoint B x
  disjoint I x
  disjoint R x
  disjoint .x. x
  disjoint .1. x
  disjoint x y
  disjoint B y
  disjoint I y
  disjoint R y
  disjoint .x. y
  disjoint .1. y
  assert |- ( R e. Ring -> ( ( I e. B /\ A. x e. B ( ( I .x. x ) = x /\ ( x .x. I ) = x ) ) <-> .1. = I ) )

  proof
    cR
    crg
    wcel
    #
    vx
    cB
    c.x
    cI
    vy
    cR
    cmgp
    cfv
    #
    c.1
    cB
    cR
    @1
    @1
    eqid
    #
    rngidm.b
    mgpbas
    cR
    c.1
    @1
    @2
    rngidm.u
    ringidval
    cR
    c.x
    @1
    @2
    rngidm.t
    mgpplusg
    @0
    vy
    cv
    #
    vx
    cv
    #
    c.x
    co
    @4
    wceq
    @4
    @3
    c.x
    co
    @4
    wceq
    wa
    vx
    cB
    wral
    #
    vy
    cB
    wreu
    @5
    vy
    cB
    wrex
    vx
    vy
    cB
    cR
    c.x
    rngidm.b
    rngidm.t
    ringideu
    @5
    vy
    cB
    reurex
    syl
    ismgmid
end
