include "wcel.mm"
include "cr.mm"
include "abvf.mm"
include "ffvelrnda.mm"

theorem abvcl
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let c.0: class .0.
  let cY: class Y
  let vf: setvar f
  let vr: setvar r
  let c.x: class .x.
  assume abvf.a: |- A = ( AbsVal ` R )
  assume abvf.b: |- B = ( Base ` R )


  assert |- ( ( F e. A /\ X e. B ) -> ( F ` X ) e. RR )

  proof
    cF
    cA
    wcel
    cB
    cr
    cX
    cF
    cA
    cB
    cR
    cF
    abvf.a
    abvf.b
    abvf
    ffvelrnda
end
