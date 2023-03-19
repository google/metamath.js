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
include "infcl.mm"

theorem infrecl
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vw: setvar w
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint A w
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  assert |- ( ( A C_ RR /\ A =/= (/) /\ E. x e. RR A. y e. A x <_ y ) -> inf ( A , RR , < ) e. RR )

  proof
    cA
    cr
    wss
    cA
    c0
    wne
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
    infm3
    infcl
end
