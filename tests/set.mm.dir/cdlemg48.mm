include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "wrex.mm"
include "ccom.mm"
include "cdlemftr1.mm"
include "3ad2ant1.mm"
include "simp11.mm"
include "simp12l.mm"
include "simp12r.mm"
include "simp2.mm"
include "simp13r.mm"
include "simp13l.mm"
include "simp3l.mm"
include "simp3r.mm"
include "cdlemg47.mm"
include "syl323anc.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem cdlemg48
  let cB: class B
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let vh: setvar h
  assume cdlemg46.b: |- B = ( Base ` K )
  assume cdlemg46.h: |- H = ( LHyp ` K )
  assume cdlemg46.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg46.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ ( F =/= ( _I |` B ) /\ ( R ` F ) = ( R ` G ) ) ) -> ( F o. G ) = ( G o. F ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    wa
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    cF
    cR
    cfv
    #
    cG
    cR
    cfv
    wceq
    #
    wa
    #
    w3a
    #
    vh
    cv
    #
    @4
    wne
    #
    @10
    cR
    cfv
    @6
    wne
    #
    wa
    #
    vh
    cT
    wrex
    #
    cF
    cG
    ccom
    cG
    cF
    ccom
    wceq
    #
    @0
    @3
    @14
    @8
    cB
    cR
    cT
    vh
    cH
    cK
    cW
    @6
    cdlemg46.b
    cdlemg46.h
    cdlemg46.t
    cdlemg46.r
    cdlemftr1
    3ad2ant1
    @9
    @13
    @15
    vh
    cT
    @9
    @10
    cT
    wcel
    #
    @13
    w3a
    @0
    @1
    @2
    @16
    @7
    @5
    @11
    @12
    @15
    @0
    @3
    @8
    @16
    @13
    simp11
    @1
    @2
    @0
    @8
    @16
    @13
    simp12l
    @1
    @2
    @0
    @8
    @16
    @13
    simp12r
    @9
    @16
    @13
    simp2
    @5
    @7
    @0
    @3
    @16
    @13
    simp13r
    @5
    @7
    @0
    @3
    @16
    @13
    simp13l
    @9
    @16
    @11
    @12
    simp3l
    @9
    @16
    @11
    @12
    simp3r
    cB
    cR
    cT
    vh
    cF
    cG
    cH
    cK
    cW
    cdlemg46.b
    cdlemg46.h
    cdlemg46.t
    cdlemg46.r
    cdlemg47
    syl323anc
    rexlimdv3a
    mpd
end
