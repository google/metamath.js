include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "ccom.mm"
include "cldil.mm"
include "cfv.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wn.mm"
include "cjn.mm"
include "co.mm"
include "cmee.mm"
include "wceq.mm"
include "wi.mm"
include "catm.mm"
include "wral.mm"
include "simp1.mm"
include "eqid.mm"
include "ltrnldil.mm"
include "3adant3.mm"
include "3adant2.mm"
include "ldilco.mm"
include "syl3anc.mm"
include "simp11.mm"
include "simp2l.mm"
include "simp3l.mm"
include "jca.mm"
include "simp2r.mm"
include "simp3r.mm"
include "simp12.mm"
include "simp13.mm"
include "cdlemg41.mm"
include "syl122anc.mm"
include "3exp.mm"
include "ralrimivv.mm"
include "wb.mm"
include "isltrn.mm"
include "3ad2ant1.mm"
include "mpbir2and.mm"

theorem ltrnco
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let vp: setvar p
  let vq: setvar q
  assume ltrnco.h: |- H = ( LHyp ` K )
  assume ltrnco.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) -> ( F o. G ) e. T )

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
    w3a
    #
    cF
    cG
    ccom
    #
    cT
    wcel
    #
    @4
    cW
    cK
    cldil
    cfv
    cfv
    #
    wcel
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
    vq
    cv
    #
    cW
    @9
    wbr
    wn
    #
    wa
    #
    @8
    @8
    @4
    cfv
    cK
    cjn
    cfv
    #
    co
    cW
    cK
    cmee
    cfv
    #
    co
    @11
    @11
    @4
    cfv
    @14
    co
    cW
    @15
    co
    wceq
    #
    wi
    #
    vq
    cK
    catm
    cfv
    #
    wral
    vp
    @18
    wral
    #
    @3
    @0
    cF
    @6
    wcel
    #
    cG
    @6
    wcel
    #
    @7
    @0
    @1
    @2
    simp1
    @0
    @1
    @20
    @2
    @6
    cT
    cF
    cH
    cK
    chlt
    cW
    ltrnco.h
    @6
    eqid
    #
    ltrnco.t
    ltrnldil
    3adant3
    @0
    @2
    @21
    @1
    @6
    cT
    cG
    cH
    cK
    chlt
    cW
    ltrnco.h
    @22
    ltrnco.t
    ltrnldil
    3adant2
    @6
    cF
    cG
    cH
    cK
    chlt
    cW
    ltrnco.h
    @22
    ldilco
    syl3anc
    @3
    @17
    vp
    vq
    @18
    @18
    @3
    @8
    @18
    wcel
    #
    @11
    @18
    wcel
    #
    wa
    #
    @13
    @16
    @3
    @25
    @13
    w3a
    #
    @0
    @23
    @10
    wa
    @24
    @12
    wa
    @1
    @2
    @16
    @0
    @1
    @2
    @25
    @13
    simp11
    @26
    @23
    @10
    @3
    @23
    @24
    @13
    simp2l
    @3
    @25
    @10
    @12
    simp3l
    jca
    @26
    @24
    @12
    @3
    @23
    @24
    @13
    simp2r
    @3
    @25
    @10
    @12
    simp3r
    jca
    @0
    @1
    @2
    @25
    @13
    simp12
    @0
    @1
    @2
    @25
    @13
    simp13
    @18
    @8
    @11
    cT
    cF
    cG
    cH
    @14
    cK
    @9
    @15
    cW
    @9
    eqid
    #
    @14
    eqid
    #
    @15
    eqid
    #
    @18
    eqid
    #
    ltrnco.h
    ltrnco.t
    cdlemg41
    syl122anc
    3exp
    ralrimivv
    @0
    @1
    @5
    @7
    @19
    wa
    wb
    @2
    @18
    chlt
    @6
    cT
    @4
    cH
    @14
    cK
    @9
    @15
    cW
    vq
    vp
    @27
    @28
    @29
    @30
    ltrnco.h
    @22
    ltrnco.t
    isltrn
    3ad2ant1
    mpbir2and
end
