include "clines2.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wmo.mm"
include "an4.mm"
include "wceq.mm"
include "cline2.mm"
include "co.mm"
include "linethru.mm"
include "3expa.mm"
include "eqtr3.mm"
include "syl2an.mm"
include "anandirs.mm"
include "ex.mm"
include "necon1d.mm"
include "an4s.mm"
include "sylan2b.mm"
include "com23.mm"
include "3impia.mm"
include "alrimivv.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "mo4.mm"
include "sylibr.mm"

theorem lineintmo
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint A y
  disjoint x y
  disjoint B y
  assert |- ( ( A e. LinesEE /\ B e. LinesEE /\ A =/= B ) -> E* x ( x e. A /\ x e. B ) )

  proof
    cA
    clines2
    wcel
    #
    cB
    clines2
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    #
    vx
    cv
    #
    cA
    wcel
    #
    @4
    cB
    wcel
    #
    wa
    #
    vy
    cv
    #
    cA
    wcel
    #
    @8
    cB
    wcel
    #
    wa
    #
    wa
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    wal
    vx
    wal
    @7
    vx
    wmo
    @3
    @14
    vx
    vy
    @0
    @1
    @2
    @14
    @0
    @1
    wa
    #
    @12
    @2
    @13
    @15
    @12
    @2
    @13
    wi
    #
    @12
    @15
    @5
    @9
    wa
    #
    @6
    @10
    wa
    #
    wa
    @16
    @5
    @6
    @9
    @10
    an4
    @0
    @17
    @1
    @18
    @16
    @0
    @17
    wa
    #
    @1
    @18
    wa
    #
    wa
    #
    @4
    @8
    cA
    cB
    @21
    @4
    @8
    wne
    #
    cA
    cB
    wceq
    #
    @19
    @20
    @22
    @23
    @19
    @22
    wa
    cA
    @4
    @8
    cline2
    co
    #
    wceq
    #
    cB
    @24
    wceq
    #
    @23
    @20
    @22
    wa
    @0
    @17
    @22
    @25
    cA
    @4
    @8
    linethru
    3expa
    @1
    @18
    @22
    @26
    cB
    @4
    @8
    linethru
    3expa
    cA
    cB
    @24
    eqtr3
    syl2an
    anandirs
    ex
    necon1d
    an4s
    sylan2b
    ex
    com23
    3impia
    alrimivv
    @7
    @11
    vx
    vy
    @13
    @5
    @9
    @6
    @10
    @4
    @8
    cA
    eleq1
    @4
    @8
    cB
    eleq1
    anbi12d
    mo4
    sylibr
end
