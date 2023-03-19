include "cmgp.mm"
include "cfv.mm"
include "eqid.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "ringidval.mm"
include "grpidval.mm"

theorem dfur2
  let vx: setvar x
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let ve: setvar e
  assume dfur2.b: |- B = ( Base ` R )
  assume dfur2.t: |- .x. = ( .r ` R )
  assume dfur2.u: |- .1. = ( 1r ` R )

  disjoint e x
  disjoint B e
  disjoint B x
  disjoint R e
  disjoint R x
  assert |- .1. = ( iota e ( e e. B /\ A. x e. B ( ( e .x. x ) = x /\ ( x .x. e ) = x ) ) )

  proof
    vx
    cB
    c.x
    ve
    cR
    cmgp
    cfv
    #
    c.1
    cB
    cR
    @0
    @0
    eqid
    #
    dfur2.b
    mgpbas
    cR
    c.x
    @0
    @1
    dfur2.t
    mgpplusg
    cR
    c.1
    @0
    @1
    dfur2.u
    ringidval
    grpidval
end
