include "cclm.mm"
include "wcel.mm"
include "clmod.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "clmlmod.mm"
include "lmodvsdi.mm"
include "sylan.mm"

theorem clmvsdi
  let cA: class A
  let c.pl: class .+
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume clmvscl.v: |- V = ( Base ` W )
  assume clmvscl.f: |- F = ( Scalar ` W )
  assume clmvscl.s: |- .x. = ( .s ` W )
  assume clmvscl.k: |- K = ( Base ` F )
  assume clmvsdir.a: |- .+ = ( +g ` W )


  assert |- ( ( W e. CMod /\ ( A e. K /\ X e. V /\ Y e. V ) ) -> ( A .x. ( X .+ Y ) ) = ( ( A .x. X ) .+ ( A .x. Y ) ) )

  proof
    cW
    cclm
    wcel
    cW
    clmod
    wcel
    cA
    cK
    wcel
    cX
    cV
    wcel
    cY
    cV
    wcel
    w3a
    cA
    cX
    cY
    c.pl
    co
    c.x
    co
    cA
    cX
    c.x
    co
    cA
    cY
    c.x
    co
    c.pl
    co
    wceq
    cW
    clmlmod
    c.pl
    cA
    c.x
    cF
    cK
    cV
    cW
    cX
    cY
    clmvscl.v
    clmvsdir.a
    clmvscl.f
    clmvscl.s
    clmvscl.k
    lmodvsdi
    sylan
end
