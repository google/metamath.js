include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cmap.mm"
include "co.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wex.mm"
include "wa.mm"
include "n0.mm"
include "w3a.mm"
include "csn.mm"
include "cen.mm"
include "wceq.mm"
include "oveq1.mm"
include "id.mm"
include "breq12d.mm"
include "vex.mm"
include "mapsnen.mm"
include "vtoclg.mm"
include "3ad2ant1.mm"
include "ensymd.mm"
include "wn.mm"
include "wss.mm"
include "simp2.mm"
include "simp3.mm"
include "snssd.mm"
include "ssdomg.mm"
include "sylc.mm"
include "snnz.mm"
include "simpl.mm"
include "necon3ai.mm"
include "ax-mp.mm"
include "mapdom2.mm"
include "sylancl.mm"
include "endomtr.mm"
include "syl2anc.mm"
include "3expia.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "3impia.mm"

theorem mapdom3
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let cC: class C


  assert |- ( ( A e. V /\ B e. W /\ B =/= (/) ) -> A ~<_ ( A ^m B ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cB
    c0
    wne
    #
    cA
    cA
    cB
    cmap
    co
    #
    cdom
    wbr
    #
    @2
    vx
    cv
    #
    cB
    wcel
    #
    vx
    wex
    @0
    @1
    wa
    #
    @4
    vx
    cB
    n0
    @7
    @6
    @4
    vx
    @0
    @1
    @6
    @4
    @0
    @1
    @6
    w3a
    #
    cA
    cA
    @5
    csn
    #
    cmap
    co
    #
    cen
    wbr
    @10
    @3
    cdom
    wbr
    #
    @4
    @8
    @10
    cA
    @0
    @1
    @10
    cA
    cen
    wbr
    #
    @6
    vy
    cv
    #
    @9
    cmap
    co
    #
    @13
    cen
    wbr
    @12
    vy
    cA
    cV
    @13
    cA
    wceq
    #
    @14
    @10
    @13
    cA
    cen
    @13
    cA
    @9
    cmap
    oveq1
    @15
    id
    breq12d
    @13
    @5
    vy
    vex
    vx
    vex
    #
    mapsnen
    vtoclg
    3ad2ant1
    ensymd
    @8
    @9
    cB
    cdom
    wbr
    #
    @9
    c0
    wceq
    #
    cA
    c0
    wceq
    #
    wa
    #
    wn
    #
    @11
    @8
    @1
    @9
    cB
    wss
    @17
    @0
    @1
    @6
    simp2
    @8
    @5
    cB
    @0
    @1
    @6
    simp3
    snssd
    @9
    cB
    cW
    ssdomg
    sylc
    @9
    c0
    wne
    @21
    @5
    @16
    snnz
    @20
    @9
    c0
    @18
    @19
    simpl
    necon3ai
    ax-mp
    @9
    cB
    cA
    mapdom2
    sylancl
    cA
    @10
    @3
    endomtr
    syl2anc
    3expia
    exlimdv
    syl5bi
    3impia
end
