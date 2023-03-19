include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "cc.mm"
include "crab.mm"
include "cab.mm"
include "caddc.mm"
include "df-rab.mm"
include "wi.mm"
include "w3a.mm"
include "simp2.mm"
include "zcn.mm"
include "3ad2ant1.mm"
include "npcand.mm"
include "eluzadd.mm"
include "ancoms.mm"
include "3adant2.mm"
include "eqeltrrd.mm"
include "3expib.mm"
include "adantr.mm"
include "eluzelcn.mm"
include "a1i.mm"
include "eluzsub.mm"
include "3expia.mm"
include "jcad.mm"
include "impbid.mm"
include "abbi1dv.mm"
include "syl5eq.mm"

theorem shftuz
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ( A e. ZZ /\ B e. ZZ ) -> { x e. CC | ( x - A ) e. ( ZZ>= ` B ) } = ( ZZ>= ` ( B + A ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
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
    cuz
    cfv
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
    cB
    cA
    caddc
    co
    #
    cuz
    cfv
    #
    @5
    vx
    cc
    df-rab
    @2
    @7
    vx
    @9
    @2
    @7
    @3
    @9
    wcel
    #
    @0
    @7
    @10
    wi
    @1
    @0
    @6
    @5
    @10
    @0
    @6
    @5
    w3a
    #
    @4
    cA
    caddc
    co
    #
    @3
    @9
    @11
    @3
    cA
    @0
    @6
    @5
    simp2
    @0
    @6
    cA
    cc
    wcel
    @5
    cA
    zcn
    3ad2ant1
    npcand
    @0
    @5
    @12
    @9
    wcel
    #
    @6
    @5
    @0
    @13
    cA
    cB
    @4
    eluzadd
    ancoms
    3adant2
    eqeltrrd
    3expib
    adantr
    @2
    @10
    @6
    @5
    @10
    @6
    wi
    @2
    @8
    @3
    eluzelcn
    a1i
    @1
    @0
    @10
    @5
    wi
    @1
    @0
    @10
    @5
    cA
    cB
    @3
    eluzsub
    3expia
    ancoms
    jcad
    impbid
    abbi1dv
    syl5eq
end
