include "csrg.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "srgidmlem.mm"
include "simprd.mm"

theorem srgridm
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cI: class I
  assume srgidm.b: |- B = ( Base ` R )
  assume srgidm.t: |- .x. = ( .r ` R )
  assume srgidm.u: |- .1. = ( 1r ` R )


  assert |- ( ( R e. SRing /\ X e. B ) -> ( X .x. .1. ) = X )

  proof
    cR
    csrg
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
    srgidm.b
    srgidm.t
    srgidm.u
    srgidmlem
    simprd
end
