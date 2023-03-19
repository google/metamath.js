include "cops.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "leatb.mm"
include "biimpa.mm"

theorem leat
  let cA: class A
  let cB: class B
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let c.0: class .0.
  assume leatom.b: |- B = ( Base ` K )
  assume leatom.l: |- .<_ = ( le ` K )
  assume leatom.z: |- .0. = ( 0. ` K )
  assume leatom.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. OP /\ X e. B /\ P e. A ) /\ X .<_ P ) -> ( X = P \/ X = .0. ) )

  proof
    cK
    cops
    wcel
    cX
    cB
    wcel
    cP
    cA
    wcel
    w3a
    cX
    cP
    c.le
    wbr
    cX
    cP
    wceq
    cX
    c.0
    wceq
    wo
    cA
    cB
    cP
    cK
    c.le
    cX
    c.0
    leatom.b
    leatom.l
    leatom.z
    leatom.a
    leatb
    biimpa
end
