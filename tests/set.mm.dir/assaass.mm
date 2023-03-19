include "casa.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "assalem.mm"
include "simpld.mm"

theorem assaass
  let cA: class A
  let cB: class B
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vw: setvar w
  let vs: setvar s
  let vt: setvar t
  assume isassa.v: |- V = ( Base ` W )
  assume isassa.f: |- F = ( Scalar ` W )
  assume isassa.b: |- B = ( Base ` F )
  assume isassa.s: |- .x. = ( .s ` W )
  assume isassa.t: |- .X. = ( .r ` W )


  assert |- ( ( W e. AssAlg /\ ( A e. B /\ X e. V /\ Y e. V ) ) -> ( ( A .x. X ) .X. Y ) = ( A .x. ( X .X. Y ) ) )

  proof
    cW
    casa
    wcel
    cA
    cB
    wcel
    cX
    cV
    wcel
    cY
    cV
    wcel
    w3a
    wa
    cA
    cX
    c.x
    co
    cY
    c.xp
    co
    cA
    cX
    cY
    c.xp
    co
    c.x
    co
    #
    wceq
    cX
    cA
    cY
    c.x
    co
    c.xp
    co
    @0
    wceq
    cA
    cB
    c.x
    c.xp
    cF
    cV
    cW
    cX
    cY
    isassa.v
    isassa.f
    isassa.b
    isassa.s
    isassa.t
    assalem
    simpld
end
