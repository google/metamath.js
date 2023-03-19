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
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "sup3.mm"
include "ax-mp.mm"

theorem sup3ii
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  assume sup3i.1: |- ( A C_ RR /\ A =/= (/) /\ E. x e. RR A. y e. A y <_ x )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- E. x e. RR ( A. y e. A -. x < y /\ A. y e. RR ( y < x -> E. z e. A y < z ) )

  proof
    cA
    cr
    wss
    cA
    c0
    wne
    vy
    cv
    #
    vx
    cv
    #
    cle
    wbr
    vy
    cA
    wral
    vx
    cr
    wrex
    w3a
    @1
    @0
    clt
    wbr
    wn
    vy
    cA
    wral
    @0
    @1
    clt
    wbr
    @0
    vz
    cv
    clt
    wbr
    vz
    cA
    wrex
    wi
    vy
    cr
    wral
    wa
    vx
    cr
    wrex
    sup3i.1
    vx
    vy
    vz
    cA
    sup3
    ax-mp
end
