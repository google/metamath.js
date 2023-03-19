include "clmod.mm"
include "wcel.mm"
include "w3a.mm"
include "csn.mm"
include "clinc.mm"
include "cfv.mm"
include "co.mm"
include "cop.mm"
include "oveq1i.mm"
include "lincvalsng.mm"
include "syl5eq.mm"

theorem lincvalsn
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cM: class M
  let cV: class V
  let cY: class Y
  let vv: setvar v
  let vk: setvar k
  let vx: setvar x
  assume lincvalsn.b: |- B = ( Base ` M )
  assume lincvalsn.s: |- S = ( Scalar ` M )
  assume lincvalsn.r: |- R = ( Base ` S )
  assume lincvalsn.t: |- .x. = ( .s ` M )
  assume lincvalsn.f: |- F = { <. V , Y >. }


  assert |- ( ( M e. LMod /\ V e. B /\ Y e. R ) -> ( F ( linC ` M ) { V } ) = ( Y .x. V ) )

  proof
    cM
    clmod
    wcel
    cV
    cB
    wcel
    cY
    cR
    wcel
    w3a
    cF
    cV
    csn
    #
    cM
    clinc
    cfv
    #
    co
    cV
    cY
    cop
    csn
    #
    @0
    @1
    co
    cY
    cV
    c.x
    co
    cF
    @2
    @0
    @1
    lincvalsn.f
    oveq1i
    cB
    cR
    cS
    c.x
    cM
    cV
    cY
    lincvalsn.b
    lincvalsn.s
    lincvalsn.r
    lincvalsn.t
    lincvalsng
    syl5eq
end
