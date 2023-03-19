include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "cr.mm"
include "abvcl.mm"
include "3adant3.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "abvge0.mm"
include "abvne0.mm"
include "ne0gt0d.mm"

theorem abvgt0
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cY: class Y
  let vf: setvar f
  let vr: setvar r
  let c.x: class .x.
  assume abvf.a: |- A = ( AbsVal ` R )
  assume abvf.b: |- B = ( Base ` R )
  assume abveq0.z: |- .0. = ( 0g ` R )


  assert |- ( ( F e. A /\ X e. B /\ X =/= .0. ) -> 0 < ( F ` X ) )

  proof
    cF
    cA
    wcel
    #
    cX
    cB
    wcel
    #
    cX
    c.0
    wne
    #
    w3a
    cX
    cF
    cfv
    #
    @0
    @1
    @3
    cr
    wcel
    @2
    cA
    cB
    cR
    cF
    cX
    abvf.a
    abvf.b
    abvcl
    3adant3
    @0
    @1
    cc0
    @3
    cle
    wbr
    @2
    cA
    cB
    cR
    cF
    cX
    abvf.a
    abvf.b
    abvge0
    3adant3
    cA
    cB
    cR
    cF
    cX
    c.0
    abvf.a
    abvf.b
    abveq0.z
    abvne0
    ne0gt0d
end
