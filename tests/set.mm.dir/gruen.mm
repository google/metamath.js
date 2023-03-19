include "cgru.mm"
include "wcel.mm"
include "wss.mm"
include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "bren.mm"
include "wfo.mm"
include "f1ofo.mm"
include "w3a.mm"
include "crn.mm"
include "wceq.mm"
include "simp3l.mm"
include "forn.mm"
include "syl.mm"
include "wf.mm"
include "fof.mm"
include "fss.mm"
include "sylan.mm"
include "grurn.mm"
include "syl3an3.mm"
include "eqeltrrd.mm"
include "3expia.mm"
include "expd.mm"
include "syl5.mm"
include "exlimdv.mm"
include "com3r.mm"
include "expdimp.mm"
include "syl7bi.mm"
include "impd.mm"
include "ancoms.mm"
include "3impia.mm"

theorem gruen
  let cA: class A
  let cB: class B
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cF: class F


  assert |- ( ( U e. Univ /\ A C_ U /\ ( B e. U /\ B ~~ A ) ) -> A e. U )

  proof
    cU
    cgru
    wcel
    #
    cA
    cU
    wss
    #
    cB
    cU
    wcel
    #
    cB
    cA
    cen
    wbr
    #
    wa
    #
    cA
    cU
    wcel
    #
    @1
    @0
    @4
    @5
    wi
    @1
    @0
    wa
    #
    @2
    @3
    @5
    @3
    cB
    cA
    vy
    cv
    #
    wf1o
    #
    vy
    wex
    #
    @6
    @2
    @5
    cB
    cA
    vy
    bren
    @1
    @0
    @2
    @9
    @5
    wi
    @0
    @2
    wa
    #
    @9
    @1
    @5
    @10
    @8
    @1
    @5
    wi
    #
    vy
    @8
    cB
    cA
    @7
    wfo
    #
    @10
    @11
    cB
    cA
    @7
    f1ofo
    @10
    @12
    @1
    @5
    @0
    @2
    @12
    @1
    wa
    #
    @5
    @0
    @2
    @13
    w3a
    #
    @7
    crn
    #
    cA
    cU
    @14
    @12
    @15
    cA
    wceq
    @0
    @2
    @12
    @1
    simp3l
    cB
    cA
    @7
    forn
    syl
    @13
    @0
    @2
    cB
    cU
    @7
    wf
    #
    @15
    cU
    wcel
    @12
    cB
    cA
    @7
    wf
    @1
    @16
    cB
    cA
    @7
    fof
    cB
    cA
    cU
    @7
    fss
    sylan
    cB
    cU
    @7
    grurn
    syl3an3
    eqeltrrd
    3expia
    expd
    syl5
    exlimdv
    com3r
    expdimp
    syl7bi
    impd
    ancoms
    3impia
end
