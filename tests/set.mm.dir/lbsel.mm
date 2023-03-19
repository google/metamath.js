include "wcel.mm"
include "lbsss.mm"
include "sselda.mm"

theorem lbsel
  let cB: class B
  let cE: class E
  let cJ: class J
  let cV: class V
  let cW: class W
  let cA: class A
  let vy: setvar y
  let vx: setvar x
  let cF: class F
  let cK: class K
  let cN: class N
  let c.x: class .x.
  let c.0: class .0.
  assume lbsss.v: |- V = ( Base ` W )
  assume lbsss.j: |- J = ( LBasis ` W )


  assert |- ( ( B e. J /\ E e. B ) -> E e. V )

  proof
    cB
    cJ
    wcel
    cB
    cV
    cE
    cB
    cJ
    cV
    cW
    lbsss.v
    lbsss.j
    lbsss
    sselda
end
