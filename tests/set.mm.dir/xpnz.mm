include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cxp.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "n0.mm"
include "anbi12i.mm"
include "eeanv.mm"
include "bitr4i.mm"
include "cop.mm"
include "opex.mm"
include "wceq.mm"
include "eleq1.mm"
include "opelxp.mm"
include "syl6bb.mm"
include "spcev.mm"
include "sylibr.mm"
include "exlimivv.mm"
include "sylbi.mm"
include "xpeq1.mm"
include "0xp.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "xpeq2.mm"
include "xp0.mm"
include "jca.mm"
include "impbii.mm"

theorem xpnz
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A =/= (/) /\ B =/= (/) ) <-> ( A X. B ) =/= (/) )

  proof
    cA
    c0
    wne
    #
    cB
    c0
    wne
    #
    wa
    #
    cA
    cB
    cxp
    #
    c0
    wne
    #
    @2
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    @4
    @2
    @6
    vx
    wex
    #
    @8
    vy
    wex
    #
    wa
    @10
    @0
    @11
    @1
    @12
    vx
    cA
    n0
    vy
    cB
    n0
    anbi12i
    @6
    @8
    vx
    vy
    eeanv
    bitr4i
    @9
    @4
    vx
    vy
    @9
    vz
    cv
    #
    @3
    wcel
    #
    vz
    wex
    @4
    @14
    @9
    vz
    @5
    @7
    cop
    #
    @5
    @7
    opex
    @13
    @15
    wceq
    @14
    @15
    @3
    wcel
    @9
    @13
    @15
    @3
    eleq1
    @5
    @7
    cA
    cB
    opelxp
    syl6bb
    spcev
    vz
    @3
    n0
    sylibr
    exlimivv
    sylbi
    @4
    @0
    @1
    cA
    c0
    @3
    c0
    cA
    c0
    wceq
    @3
    c0
    cB
    cxp
    c0
    cA
    c0
    cB
    xpeq1
    cB
    0xp
    syl6eq
    necon3i
    cB
    c0
    @3
    c0
    cB
    c0
    wceq
    @3
    cA
    c0
    cxp
    c0
    cB
    c0
    cA
    xpeq2
    cA
    xp0
    syl6eq
    necon3i
    jca
    impbii
end
