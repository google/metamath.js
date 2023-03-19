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
include "weq.mm"
include "wo.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "wcel.mm"
include "wb.mm"
include "ssel.mm"
include "leloe.mm"
include "expcom.mm"
include "syl9.mm"
include "imp31.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "anbi2d.mm"
include "pm5.32i.mm"
include "3anass.mm"
include "3bitr4i.mm"
include "sup2.mm"
include "sylbi.mm"

theorem sup3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint t x
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint t y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint t z
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
  assert |- ( ( A C_ RR /\ A =/= (/) /\ E. x e. RR A. y e. A y <_ x ) -> E. x e. RR ( A. y e. A -. x < y /\ A. y e. RR ( y < x -> E. z e. A y < z ) ) )

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
    #
    vx
    cv
    #
    cle
    wbr
    #
    vy
    cA
    wral
    #
    vx
    cr
    wrex
    #
    w3a
    #
    @0
    @1
    @2
    @3
    clt
    wbr
    #
    vy
    vx
    weq
    wo
    #
    vy
    cA
    wral
    #
    vx
    cr
    wrex
    #
    w3a
    #
    @3
    @2
    clt
    wbr
    wn
    vy
    cA
    wral
    @8
    @2
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
    @0
    @1
    @6
    wa
    #
    wa
    @0
    @1
    @11
    wa
    #
    wa
    @7
    @12
    @0
    @13
    @14
    @0
    @6
    @11
    @1
    @0
    @5
    @10
    vx
    cr
    @0
    @3
    cr
    wcel
    #
    wa
    @4
    @9
    vy
    cA
    @0
    @15
    @2
    cA
    wcel
    #
    @4
    @9
    wb
    #
    @0
    @16
    @2
    cr
    wcel
    #
    @15
    @17
    cA
    cr
    @2
    ssel
    @18
    @15
    @17
    @2
    @3
    leloe
    expcom
    syl9
    imp31
    ralbidva
    rexbidva
    anbi2d
    pm5.32i
    @0
    @1
    @6
    3anass
    @0
    @1
    @11
    3anass
    3bitr4i
    vx
    vy
    vz
    cA
    sup2
    sylbi
end
