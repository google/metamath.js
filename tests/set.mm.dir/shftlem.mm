include "cc.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "crab.mm"
include "cab.mm"
include "caddc.mm"
include "wceq.mm"
include "wrex.mm"
include "df-rab.mm"
include "wi.mm"
include "npcan.mm"
include "ancoms.mm"
include "eqcomd.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "expcom.mm"
include "syl.mm"
include "expimpd.mm"
include "adantr.mm"
include "ssel2.mm"
include "addcl.mm"
include "sylan.mm"
include "pncan.mm"
include "simplr.mm"
include "eqeltrd.mm"
include "jca.mm"
include "anassrs.mm"
include "eleq1.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "abbidv.mm"
include "syl5eq.mm"

theorem shftlem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- ( ( A e. CC /\ B C_ CC ) -> { x e. CC | ( x - A ) e. B } = { x | E. y e. B x = ( y + A ) } )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wss
    #
    wa
    #
    vx
    cv
    #
    cA
    cmin
    co
    #
    cB
    wcel
    #
    vx
    cc
    crab
    @3
    cc
    wcel
    #
    @5
    wa
    #
    vx
    cab
    @3
    vy
    cv
    #
    cA
    caddc
    co
    #
    wceq
    #
    vy
    cB
    wrex
    #
    vx
    cab
    @5
    vx
    cc
    df-rab
    @2
    @7
    @11
    vx
    @2
    @7
    @11
    @0
    @7
    @11
    wi
    @1
    @0
    @6
    @5
    @11
    @0
    @6
    wa
    #
    @3
    @4
    cA
    caddc
    co
    #
    wceq
    #
    @5
    @11
    wi
    @12
    @13
    @3
    @6
    @0
    @13
    @3
    wceq
    @3
    cA
    npcan
    ancoms
    eqcomd
    @5
    @14
    @11
    @10
    @14
    vy
    @4
    cB
    @8
    @4
    wceq
    @9
    @13
    @3
    @8
    @4
    cA
    caddc
    oveq1
    eqeq2d
    rspcev
    expcom
    syl
    expimpd
    adantr
    @2
    @10
    @7
    vy
    cB
    @2
    @8
    cB
    wcel
    #
    wa
    @7
    @10
    @9
    cc
    wcel
    #
    @9
    cA
    cmin
    co
    #
    cB
    wcel
    #
    wa
    #
    @0
    @1
    @15
    @19
    @1
    @15
    wa
    #
    @0
    @19
    @20
    @0
    wa
    #
    @16
    @18
    @20
    @8
    cc
    wcel
    #
    @0
    @16
    cB
    cc
    @8
    ssel2
    #
    @8
    cA
    addcl
    sylan
    @21
    @17
    @8
    cB
    @20
    @22
    @0
    @17
    @8
    wceq
    @23
    @8
    cA
    pncan
    sylan
    @1
    @15
    @0
    simplr
    eqeltrd
    jca
    ancoms
    anassrs
    @10
    @6
    @16
    @5
    @18
    @3
    @9
    cc
    eleq1
    @10
    @4
    @17
    cB
    @3
    @9
    cA
    cmin
    oveq1
    eleq1d
    anbi12d
    syl5ibrcom
    rexlimdva
    impbid
    abbidv
    syl5eq
end
