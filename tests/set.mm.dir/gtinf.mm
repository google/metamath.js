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
include "wcel.mm"
include "clt.mm"
include "cinf.mm"
include "wa.mm"
include "simprl.mm"
include "simprr.mm"
include "wor.mm"
include "ltso.mm"
include "a1i.mm"
include "wn.mm"
include "wi.mm"
include "infm3.mm"
include "adantr.mm"
include "infglb.mm"
include "mp2and.mm"

theorem gtinf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cS: class S

  disjoint A z
  disjoint x y
  disjoint x z
  disjoint S x
  disjoint y z
  disjoint S y
  disjoint S z
  assert |- ( ( ( S C_ RR /\ S =/= (/) /\ E. x e. RR A. y e. S x <_ y ) /\ ( A e. RR /\ inf ( S , RR , < ) < A ) ) -> E. z e. S z < A )

  proof
    cS
    cr
    wss
    cS
    c0
    wne
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    vy
    cS
    wral
    vx
    cr
    wrex
    w3a
    #
    cA
    cr
    wcel
    #
    cS
    cr
    clt
    cinf
    cA
    clt
    wbr
    #
    wa
    #
    wa
    #
    @3
    @4
    vz
    cv
    #
    cA
    clt
    wbr
    vz
    cS
    wrex
    @2
    @3
    @4
    simprl
    @2
    @3
    @4
    simprr
    @6
    vx
    vy
    vz
    cr
    cS
    cA
    clt
    cr
    clt
    wor
    @6
    ltso
    a1i
    @2
    @1
    @0
    clt
    wbr
    wn
    vy
    cS
    wral
    @0
    @1
    clt
    wbr
    @7
    @1
    clt
    wbr
    vz
    cS
    wrex
    wi
    vy
    cr
    wral
    wa
    vx
    cr
    wrex
    @5
    vx
    vy
    vz
    cS
    infm3
    adantr
    infglb
    mp2and
end
