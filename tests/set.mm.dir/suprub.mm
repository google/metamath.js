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
include "wa.mm"
include "clt.mm"
include "csup.mm"
include "wn.mm"
include "wor.mm"
include "ltso.mm"
include "a1i.mm"
include "sup3.mm"
include "supub.mm"
include "imp.mm"
include "simp1.mm"
include "sselda.mm"
include "suprcl.mm"
include "adantr.mm"
include "lenltd.mm"
include "mpbird.mm"

theorem suprub
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
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
  assert |- ( ( ( A C_ RR /\ A =/= (/) /\ E. x e. RR A. y e. A y <_ x ) /\ B e. A ) -> B <_ sup ( A , RR , < ) )

  proof
    cA
    cr
    wss
    #
    cA
    c0
    wne
    #
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
    #
    w3a
    #
    cB
    cA
    wcel
    #
    wa
    #
    cB
    cA
    cr
    clt
    csup
    #
    cle
    wbr
    @6
    cB
    clt
    wbr
    wn
    #
    @3
    @4
    @7
    @3
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
    sup3
    supub
    imp
    @5
    cB
    @6
    @3
    cA
    cr
    cB
    @0
    @1
    @2
    simp1
    sselda
    @3
    @6
    cr
    wcel
    @4
    vx
    vy
    cA
    suprcl
    adantr
    lenltd
    mpbird
end
