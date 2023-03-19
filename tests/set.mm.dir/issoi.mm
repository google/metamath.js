include "wor.mm"
include "wtru.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "adantl.mm"
include "w3a.mm"
include "wa.mm"
include "wi.mm"
include "ispod.mm"
include "weq.mm"
include "w3o.mm"
include "issod.mm"
include "trud.mm"

theorem issoi
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  assume issoi.1: |- ( x e. A -> -. x R x )
  assume issoi.2: |- ( ( x e. A /\ y e. A /\ z e. A ) -> ( ( x R y /\ y R z ) -> x R z ) )
  assume issoi.3: |- ( ( x e. A /\ y e. A ) -> ( x R y \/ x = y \/ y R x ) )

  disjoint x y
  disjoint x z
  disjoint R x
  disjoint y z
  disjoint R y
  disjoint R z
  disjoint A x
  disjoint A y
  disjoint A z
  assert |- R Or A

  proof
    cA
    cR
    wor
    wtru
    vx
    vy
    cA
    cR
    wtru
    vx
    vy
    vz
    cA
    cR
    vx
    cv
    #
    cA
    wcel
    #
    @0
    @0
    cR
    wbr
    wn
    wtru
    issoi.1
    adantl
    @1
    vy
    cv
    #
    cA
    wcel
    #
    vz
    cv
    #
    cA
    wcel
    w3a
    @0
    @2
    cR
    wbr
    #
    @2
    @4
    cR
    wbr
    wa
    @0
    @4
    cR
    wbr
    wi
    wtru
    issoi.2
    adantl
    ispod
    @1
    @3
    wa
    @5
    vx
    vy
    weq
    @2
    @0
    cR
    wbr
    w3o
    wtru
    issoi.3
    adantl
    issod
    trud
end
