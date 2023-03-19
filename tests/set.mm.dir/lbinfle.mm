include "cr.mm"
include "wss.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wcel.mm"
include "w3a.mm"
include "clt.mm"
include "cinf.mm"
include "crio.mm"
include "wceq.mm"
include "lbinf.mm"
include "3adant3.mm"
include "lble.mm"
include "eqbrtrd.mm"

theorem lbinfle
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cS: class S
  let vz: setvar z

  disjoint S x
  disjoint S y
  disjoint x y
  disjoint A y
  disjoint S z
  disjoint x z
  disjoint y z
  assert |- ( ( S C_ RR /\ E. x e. S A. y e. S x <_ y /\ A e. S ) -> inf ( S , RR , < ) <_ A )

  proof
    cS
    cr
    wss
    #
    vx
    cv
    vy
    cv
    cle
    wbr
    vy
    cS
    wral
    #
    vx
    cS
    wrex
    #
    cA
    cS
    wcel
    #
    w3a
    cS
    cr
    clt
    cinf
    #
    @1
    vx
    cS
    crio
    #
    cA
    cle
    @0
    @2
    @4
    @5
    wceq
    @3
    vx
    vy
    cS
    lbinf
    3adant3
    vx
    vy
    cA
    cS
    lble
    eqbrtrd
end
