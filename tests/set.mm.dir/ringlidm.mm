include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "ringidmlem.mm"
include "simpld.mm"

theorem ringlidm
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cI: class I
  assume rngidm.b: |- B = ( Base ` R )
  assume rngidm.t: |- .x. = ( .r ` R )
  assume rngidm.u: |- .1. = ( 1r ` R )


  assert |- ( ( R e. Ring /\ X e. B ) -> ( .1. .x. X ) = X )

  proof
    cR
    crg
    wcel
    cX
    cB
    wcel
    wa
    c.1
    cX
    c.x
    co
    cX
    wceq
    cX
    c.1
    c.x
    co
    cX
    wceq
    cB
    cR
    c.x
    c.1
    cX
    rngidm.b
    rngidm.t
    rngidm.u
    ringidmlem
    simpld
end
