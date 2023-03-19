include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wn.mm"
include "catm.mm"
include "wrex.mm"
include "ccom.mm"
include "wceq.mm"
include "eqid.mm"
include "lhpexnle.mm"
include "3ad2ant1.mm"
include "simp11.mm"
include "simp12l.mm"
include "simp12r.mm"
include "ltrnco.mm"
include "syl3anc.mm"
include "3simpc.mm"
include "simp13.mm"
include "cdlemg44b.mm"
include "syl131anc.mm"
include "simp12.mm"
include "simp2.mm"
include "ltrncoval.mm"
include "syl121anc.mm"
include "3eqtr4d.mm"
include "cdlemd.mm"
include "syl311anc.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem cdlemg44
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let vp: setvar p
  assume cdlemg44.h: |- H = ( LHyp ` K )
  assume cdlemg44.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg44.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ ( R ` F ) =/= ( R ` G ) ) -> ( F o. G ) = ( G o. F ) )

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
    cR
    cfv
    cG
    cR
    cfv
    wne
    #
    w3a
    #
    vp
    cv
    #
    cW
    cK
    cple
    cfv
    #
    wbr
    wn
    #
    vp
    cK
    catm
    cfv
    #
    wrex
    #
    cF
    cG
    ccom
    #
    cG
    cF
    ccom
    #
    wceq
    #
    @0
    @3
    @10
    @4
    @9
    cH
    cK
    @7
    cW
    vp
    @7
    eqid
    #
    @9
    eqid
    #
    cdlemg44.h
    lhpexnle
    3ad2ant1
    @5
    @8
    @13
    vp
    @9
    @5
    @6
    @9
    wcel
    #
    @8
    w3a
    #
    @0
    @11
    cT
    wcel
    #
    @12
    cT
    wcel
    #
    @16
    @8
    wa
    #
    @6
    @11
    cfv
    #
    @6
    @12
    cfv
    #
    wceq
    @13
    @0
    @3
    @4
    @16
    @8
    simp11
    #
    @17
    @0
    @1
    @2
    @18
    @23
    @1
    @2
    @0
    @4
    @16
    @8
    simp12l
    #
    @1
    @2
    @0
    @4
    @16
    @8
    simp12r
    #
    cT
    cF
    cG
    cH
    cK
    cW
    cdlemg44.h
    cdlemg44.t
    ltrnco
    syl3anc
    @17
    @0
    @2
    @1
    @19
    @23
    @25
    @24
    cT
    cG
    cF
    cH
    cK
    cW
    cdlemg44.h
    cdlemg44.t
    ltrnco
    syl3anc
    @5
    @16
    @8
    3simpc
    #
    @17
    @6
    cG
    cfv
    cF
    cfv
    #
    @6
    cF
    cfv
    cG
    cfv
    #
    @21
    @22
    @17
    @0
    @1
    @2
    @20
    @4
    @27
    @28
    wceq
    @23
    @24
    @25
    @26
    @0
    @3
    @4
    @16
    @8
    simp13
    @9
    @6
    cR
    cT
    cF
    cG
    cH
    cK
    @7
    cW
    cdlemg44.h
    cdlemg44.t
    cdlemg44.r
    @14
    @15
    cdlemg44b
    syl131anc
    @17
    @0
    @3
    @16
    @21
    @27
    wceq
    @23
    @0
    @3
    @4
    @16
    @8
    simp12
    @5
    @16
    @8
    simp2
    #
    @9
    @6
    cT
    cF
    cG
    cH
    cK
    @7
    cW
    @14
    @15
    cdlemg44.h
    cdlemg44.t
    ltrncoval
    syl3anc
    @17
    @0
    @2
    @1
    @16
    @22
    @28
    wceq
    @23
    @25
    @24
    @29
    @9
    @6
    cT
    cG
    cF
    cH
    cK
    @7
    cW
    @14
    @15
    cdlemg44.h
    cdlemg44.t
    ltrncoval
    syl121anc
    3eqtr4d
    @9
    @6
    cT
    @11
    @12
    cH
    cK
    @7
    cW
    @14
    @15
    cdlemg44.h
    cdlemg44.t
    cdlemd
    syl311anc
    rexlimdv3a
    mpd
end
