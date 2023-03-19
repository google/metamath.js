include "con0.mm"
include "wcel.mm"
include "cv.mm"
include "cale.mm"
include "cfv.mm"
include "cen.mm"
include "wbr.mm"
include "crab.mm"
include "csuc.mm"
include "cdif.mm"
include "cdom.mm"
include "csdm.mm"
include "alephsuc2.mm"
include "wceq.mm"
include "ccrd.mm"
include "alephcard.mm"
include "cdm.mm"
include "alephon.mm"
include "onenon.mm"
include "ax-mp.mm"
include "cardval2.mm"
include "eqtr3i.mm"
include "a1i.mm"
include "difeq12d.mm"
include "wn.mm"
include "wa.mm"
include "difrab.mm"
include "bren2.mm"
include "rabbii.mm"
include "eqtr4i.mm"
include "syl6req.mm"
include "com.mm"
include "mp1i.mm"
include "wss.mm"
include "sucelon.mm"
include "alephgeom.mm"
include "bitri.mm"
include "cvv.mm"
include "wi.mm"
include "fvex.mm"
include "ssdomg.mm"
include "sylbi.mm"
include "alephordilem1.mm"
include "infdif.mm"
include "syl3anc.mm"
include "eqbrtrd.mm"
include "ensymd.mm"

theorem alephsuc3
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. On -> ( aleph ` suc A ) ~~ { x e. On | x ~~ ( aleph ` A ) } )

  proof
    cA
    con0
    wcel
    #
    vx
    cv
    #
    cA
    cale
    cfv
    #
    cen
    wbr
    #
    vx
    con0
    crab
    #
    cA
    csuc
    #
    cale
    cfv
    #
    @0
    @4
    @6
    @2
    cdif
    #
    @6
    cen
    @0
    @7
    @1
    @2
    cdom
    wbr
    #
    vx
    con0
    crab
    #
    @1
    @2
    csdm
    wbr
    #
    vx
    con0
    crab
    #
    cdif
    #
    @4
    @0
    @6
    @9
    @2
    @11
    vx
    cA
    alephsuc2
    @2
    @11
    wceq
    @0
    @2
    ccrd
    cfv
    #
    @2
    @11
    cA
    alephcard
    @2
    ccrd
    cdm
    #
    wcel
    #
    @13
    @11
    wceq
    @2
    con0
    wcel
    @15
    cA
    alephon
    @2
    onenon
    ax-mp
    vx
    @2
    cardval2
    ax-mp
    eqtr3i
    a1i
    difeq12d
    @12
    @8
    @10
    wn
    wa
    #
    vx
    con0
    crab
    @4
    @8
    @10
    vx
    con0
    difrab
    @3
    @16
    vx
    con0
    @1
    @2
    bren2
    rabbii
    eqtr4i
    syl6req
    @0
    @6
    @14
    wcel
    #
    com
    @6
    cdom
    wbr
    #
    @2
    @6
    csdm
    wbr
    @7
    @6
    cen
    wbr
    @6
    con0
    wcel
    @17
    @0
    @5
    alephon
    @6
    onenon
    mp1i
    @0
    com
    @6
    wss
    #
    @18
    @0
    @5
    con0
    wcel
    @19
    cA
    sucelon
    @5
    alephgeom
    bitri
    @6
    cvv
    wcel
    @19
    @18
    wi
    @5
    cale
    fvex
    com
    @6
    cvv
    ssdomg
    ax-mp
    sylbi
    cA
    alephordilem1
    @6
    @2
    infdif
    syl3anc
    eqbrtrd
    ensymd
end
