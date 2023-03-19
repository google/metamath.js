include "con0.mm"
include "wcel.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "cale.mm"
include "csuc.mm"
include "wa.mm"
include "wn.mm"
include "wi.mm"
include "csdm.mm"
include "wbr.mm"
include "wb.mm"
include "cdm.mm"
include "alephon.mm"
include "id.mm"
include "cardon.mm"
include "syl6eqelr.mm"
include "onenon.mm"
include "syl.mm"
include "cardsdomel.mm"
include "sylancr.mm"
include "eleq2.mm"
include "bitrd.mm"
include "adantl.mm"
include "cv.mm"
include "crab.mm"
include "cint.mm"
include "char.mm"
include "alephsuc.mm"
include "harval2.mm"
include "mp2b.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "breq2.mm"
include "onnminsb.mm"
include "sylan9.mm"
include "con2d.mm"
include "sylan2.mm"
include "sylbird.mm"
include "imnan.mm"
include "sylib.mm"
include "ex.mm"
include "c0.mm"
include "n0i.mm"
include "wfn.mm"
include "alephfnon.mm"
include "fndm.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "ndmfv.mm"
include "sylnbir.mm"
include "nsyl2.mm"
include "sucelon.mm"
include "sylibr.mm"
include "con3i.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem alephnbtwn
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( card ` B ) = B -> -. ( ( aleph ` A ) e. B /\ B e. ( aleph ` suc A ) ) )

  proof
    cA
    con0
    wcel
    #
    cB
    ccrd
    cfv
    #
    cB
    wceq
    #
    cA
    cale
    cfv
    #
    cB
    wcel
    #
    cB
    cA
    csuc
    #
    cale
    cfv
    #
    wcel
    #
    wa
    #
    wn
    #
    wi
    @0
    @2
    @9
    @0
    @2
    wa
    #
    @4
    @7
    wn
    #
    wi
    @9
    @10
    @4
    @3
    cB
    csdm
    wbr
    #
    @11
    @2
    @12
    @4
    wb
    @0
    @2
    @12
    @3
    @1
    wcel
    #
    @4
    @2
    @3
    con0
    wcel
    #
    cB
    ccrd
    cdm
    #
    wcel
    #
    @12
    @13
    wb
    cA
    alephon
    #
    @2
    cB
    con0
    wcel
    #
    @16
    @2
    cB
    @1
    con0
    @2
    id
    cB
    cardon
    syl6eqelr
    #
    cB
    onenon
    syl
    @3
    cB
    cardsdomel
    sylancr
    @1
    cB
    @3
    eleq2
    bitrd
    adantl
    @2
    @0
    @18
    @12
    @11
    wi
    @19
    @0
    @18
    wa
    @7
    @12
    @0
    @7
    cB
    @3
    vx
    cv
    #
    csdm
    wbr
    #
    vx
    con0
    crab
    cint
    #
    wcel
    #
    @18
    @12
    wn
    @0
    @7
    @23
    @0
    @6
    @22
    cB
    @0
    @6
    @3
    char
    cfv
    #
    @22
    cA
    alephsuc
    @14
    @3
    @15
    wcel
    @24
    @22
    wceq
    @17
    @3
    onenon
    vx
    @3
    harval2
    mp2b
    syl6eq
    eleq2d
    biimpd
    @21
    @12
    vx
    cB
    @20
    cB
    @3
    csdm
    breq2
    onnminsb
    sylan9
    con2d
    sylan2
    sylbird
    @4
    @7
    imnan
    sylib
    ex
    @0
    wn
    @9
    @2
    @8
    @0
    @7
    @0
    @4
    @7
    @5
    con0
    wcel
    #
    @0
    @7
    @6
    c0
    wceq
    #
    @25
    @6
    cB
    n0i
    @25
    @5
    cale
    cdm
    #
    wcel
    @26
    @27
    con0
    @5
    cale
    con0
    wfn
    @27
    con0
    wceq
    alephfnon
    con0
    cale
    fndm
    ax-mp
    eleq2i
    @5
    cale
    ndmfv
    sylnbir
    nsyl2
    cA
    sucelon
    sylibr
    adantl
    con3i
    a1d
    pm2.61i
end
