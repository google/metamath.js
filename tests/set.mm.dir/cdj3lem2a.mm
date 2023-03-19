include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "cph.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "cva.mm"
include "wrex.mm"
include "shseli.mm"
include "wa.mm"
include "w3a.mm"
include "cdj3lem2.mm"
include "simp1.mm"
include "eqeltrd.mm"
include "3expa.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "syl5ibr.mm"
include "expd.mm"
include "com13.mm"
include "rexlimdvv.mm"
include "syl5bi.mm"
include "impcom.mm"

theorem cdj3lem2a
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let vu: setvar u
  let vv: setvar v
  let vt: setvar t
  let vh: setvar h
  let vy: setvar y
  let cD: class D
  assume cdj3lem2.1: |- A e. SH
  assume cdj3lem2.2: |- B e. SH
  assume cdj3lem2.3: |- S = ( x e. ( A +H B ) |-> ( iota_ z e. A E. w e. B x = ( z +h w ) ) )

  disjoint x z
  disjoint w x
  disjoint A x
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B x
  disjoint B z
  disjoint B w
  disjoint C x
  disjoint C z
  disjoint C w
  disjoint u v
  disjoint t v
  disjoint h v
  disjoint S v
  disjoint t u
  disjoint h u
  disjoint S u
  disjoint h t
  disjoint S t
  disjoint S h
  disjoint x y
  disjoint v x
  disjoint u x
  disjoint t x
  disjoint h x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint t y
  disjoint h y
  disjoint A y
  disjoint v z
  disjoint u z
  disjoint t z
  disjoint h z
  disjoint v w
  disjoint u w
  disjoint t w
  disjoint h w
  disjoint u v
  disjoint t v
  disjoint h v
  disjoint A v
  disjoint t u
  disjoint h u
  disjoint A u
  disjoint h t
  disjoint A t
  disjoint A h
  disjoint B y
  disjoint B v
  disjoint B u
  disjoint B t
  disjoint B h
  disjoint C y
  disjoint C v
  disjoint C u
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint D w
  assert |- ( ( C e. ( A +H B ) /\ ( A i^i B ) = 0H ) -> ( S ` C ) e. A )

  proof
    cA
    cB
    cin
    c0h
    wceq
    #
    cC
    cA
    cB
    cph
    co
    wcel
    #
    cC
    cS
    cfv
    #
    cA
    wcel
    #
    @1
    cC
    vv
    cv
    #
    vu
    cv
    #
    cva
    co
    #
    wceq
    #
    vu
    cB
    wrex
    vv
    cA
    wrex
    @0
    @3
    vv
    vu
    cA
    cB
    cC
    cdj3lem2.1
    cdj3lem2.2
    shseli
    @0
    @7
    @3
    vv
    vu
    cA
    cB
    @7
    @4
    cA
    wcel
    #
    @5
    cB
    wcel
    #
    wa
    #
    @0
    @3
    @7
    @10
    @0
    @3
    @10
    @0
    wa
    @3
    @7
    @6
    cS
    cfv
    #
    cA
    wcel
    #
    @8
    @9
    @0
    @12
    @8
    @9
    @0
    w3a
    @11
    @4
    cA
    vx
    vz
    vw
    cA
    cB
    @4
    @5
    cS
    cdj3lem2.1
    cdj3lem2.2
    cdj3lem2.3
    cdj3lem2
    @8
    @9
    @0
    simp1
    eqeltrd
    3expa
    @7
    @2
    @11
    cA
    cC
    @6
    cS
    fveq2
    eleq1d
    syl5ibr
    expd
    com13
    rexlimdvv
    syl5bi
    impcom
end
