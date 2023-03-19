include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "clt.mm"
include "wor.mm"
include "ltso.mm"
include "a1i.mm"
include "sup3.mm"
include "supcl.mm"

theorem suprcl
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint t x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint t y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint t z
  disjoint A z
  disjoint v w
  disjoint u w
  disjoint t w
  disjoint A w
  disjoint u v
  disjoint t v
  disjoint A v
  disjoint t u
  disjoint A u
  disjoint A t
  assert |- ( ( A C_ RR /\ A =/= (/) /\ E. x e. RR A. y e. A y <_ x ) -> sup ( A , RR , < ) e. RR )

  proof
    cA
    cr
    wss
    cA
    c0
    wne
    vy
    cv
    vx
    cv
    cle
    wbr
    vy
    cA
    wral
    vx
    cr
    wrex
    w3a
    #
    vx
    vy
    vz
    cr
    cA
    clt
    cr
    clt
    wor
    @0
    ltso
    a1i
    vx
    vy
    vz
    cA
    sup3
    supcl
end
