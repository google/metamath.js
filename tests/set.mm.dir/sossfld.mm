include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cv.mm"
include "wne.mm"
include "eldifsn.mm"
include "wbr.mm"
include "wo.mm"
include "wb.mm"
include "sotrieq.mm"
include "necon2abid.mm"
include "anass1rs.mm"
include "wi.mm"
include "breldmg.mm"
include "3expia.mm"
include "ancoms.mm"
include "brelrng.mm"
include "orim12d.mm"
include "elun.mm"
include "syl6ibr.mm"
include "adantll.mm"
include "sylbird.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "ssrdv.mm"

theorem sossfld
  let cA: class A
  let cB: class B
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( R Or A /\ B e. A ) -> ( A \ { B } ) C_ ( dom R u. ran R ) )

  proof
    cA
    cR
    wor
    #
    cB
    cA
    wcel
    #
    wa
    #
    vx
    cA
    cB
    csn
    cdif
    #
    cR
    cdm
    #
    cR
    crn
    #
    cun
    #
    vx
    cv
    #
    @3
    wcel
    @7
    cA
    wcel
    #
    @7
    cB
    wne
    #
    wa
    @2
    @7
    @6
    wcel
    #
    @7
    cA
    cB
    eldifsn
    @2
    @8
    @9
    @10
    @2
    @8
    wa
    @9
    @7
    cB
    cR
    wbr
    #
    cB
    @7
    cR
    wbr
    #
    wo
    #
    @10
    @0
    @8
    @1
    @13
    @9
    wb
    @0
    @8
    @1
    wa
    wa
    @13
    @7
    cB
    cA
    @7
    cB
    cR
    sotrieq
    necon2abid
    anass1rs
    @1
    @8
    @13
    @10
    wi
    @0
    @1
    @8
    wa
    #
    @13
    @7
    @4
    wcel
    #
    @7
    @5
    wcel
    #
    wo
    @10
    @14
    @11
    @15
    @12
    @16
    @8
    @1
    @11
    @15
    wi
    @8
    @1
    @11
    @15
    @7
    cB
    cA
    cA
    cR
    breldmg
    3expia
    ancoms
    @1
    @8
    @12
    @16
    cB
    @7
    cR
    cA
    cA
    brelrng
    3expia
    orim12d
    @7
    @4
    @5
    elun
    syl6ibr
    adantll
    sylbird
    expimpd
    syl5bi
    ssrdv
end
