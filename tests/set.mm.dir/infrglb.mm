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
include "infm3.mm"
include "simp1.mm"
include "infglbb.mm"

theorem infrglb
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B z
  assert |- ( ( ( A C_ RR /\ A =/= (/) /\ E. x e. RR A. y e. A x <_ y ) /\ B e. RR ) -> ( inf ( A , RR , < ) < B <-> E. z e. A z < B ) )

  proof
    cA
    cr
    wss
    #
    cA
    c0
    wne
    #
    vx
    cv
    vy
    cv
    cle
    wbr
    vy
    cA
    wral
    vx
    cr
    wrex
    #
    w3a
    #
    vx
    vy
    vz
    cr
    cA
    cB
    clt
    cr
    clt
    wor
    @3
    ltso
    a1i
    vx
    vy
    vz
    cA
    infm3
    @0
    @1
    @2
    simp1
    infglbb
end
