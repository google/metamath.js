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
include "csup.mm"
include "wcel.mm"
include "suprcl.mm"
include "ax-mp.mm"

theorem suprclii
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume sup3i.1: |- ( A C_ RR /\ A =/= (/) /\ E. x e. RR A. y e. A y <_ x )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- sup ( A , RR , < ) e. RR

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
    cA
    cr
    clt
    csup
    cr
    wcel
    sup3i.1
    vx
    vy
    cA
    suprcl
    ax-mp
end
