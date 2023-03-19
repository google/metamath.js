include "cobs.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "simp3.mm"
include "cv.mm"
include "wa.mm"
include "c0g.mm"
include "wne.mm"
include "eqid.mm"
include "obsne0.mm"
include "3ad2antl1.mm"
include "wn.mm"
include "cocv.mm"
include "wceq.mm"
include "wb.mm"
include "obselocv.mm"
include "3expa.mm"
include "3adantl2.mm"
include "csn.mm"
include "simpl2.mm"
include "obsocv.mm"
include "syl.mm"
include "eleq2d.mm"
include "elsni.mm"
include "syl6bi.mm"
include "sylbird.mm"
include "necon1ad.mm"
include "mpd.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem obs2ss
  let cB: class B
  let cC: class C
  let cW: class W
  let vx: setvar x


  assert |- ( ( B e. ( OBasis ` W ) /\ C e. ( OBasis ` W ) /\ C C_ B ) -> C = B )

  proof
    cB
    cW
    cobs
    cfv
    #
    wcel
    #
    cC
    @0
    wcel
    #
    cC
    cB
    wss
    #
    w3a
    #
    cC
    cB
    @1
    @2
    @3
    simp3
    @4
    vx
    cB
    cC
    @4
    vx
    cv
    #
    cB
    wcel
    #
    @5
    cC
    wcel
    #
    @4
    @6
    wa
    #
    @5
    cW
    c0g
    cfv
    #
    wne
    #
    @7
    @1
    @2
    @6
    @10
    @3
    @5
    cB
    cW
    @9
    @9
    eqid
    #
    obsne0
    3ad2antl1
    @8
    @7
    @5
    @9
    @8
    @7
    wn
    #
    @5
    cC
    cW
    cocv
    cfv
    #
    cfv
    #
    wcel
    #
    @5
    @9
    wceq
    #
    @1
    @3
    @6
    @15
    @12
    wb
    #
    @2
    @1
    @3
    @6
    @17
    @5
    cB
    cC
    @13
    cW
    @13
    eqid
    #
    obselocv
    3expa
    3adantl2
    @8
    @15
    @5
    @9
    csn
    #
    wcel
    @16
    @8
    @14
    @19
    @5
    @8
    @2
    @14
    @19
    wceq
    @1
    @2
    @3
    @6
    simpl2
    cC
    @13
    cW
    @9
    @11
    @18
    obsocv
    syl
    eleq2d
    @5
    @9
    elsni
    syl6bi
    sylbird
    necon1ad
    mpd
    ex
    ssrdv
    eqssd
end
