include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "abveq0.mm"
include "necon3bid.mm"
include "biimp3ar.mm"

theorem abvne0
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


  assert |- ( ( F e. A /\ X e. B /\ X =/= .0. ) -> ( F ` X ) =/= 0 )

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
    cF
    cfv
    #
    cc0
    wne
    cX
    c.0
    wne
    @0
    @1
    wa
    @2
    cc0
    cX
    c.0
    cA
    cB
    cR
    cF
    cX
    c.0
    abvf.a
    abvf.b
    abveq0.z
    abveq0
    necon3bid
    biimp3ar
end
