include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cfv.mm"
include "cple.mm"
include "wbr.mm"
include "wceq.mm"
include "simp1.mm"
include "simp21.mm"
include "simp23.mm"
include "eqid.mm"
include "tendotp.mm"
include "syl3anc.mm"
include "cal.mm"
include "catm.mm"
include "wb.mm"
include "simp1l.mm"
include "hlatl.mm"
include "syl.mm"
include "tendocl.mm"
include "simp32.mm"
include "trlnidat.mm"
include "simp31.mm"
include "atcmp.mm"
include "mpbid.mm"
include "simp22.mm"
include "simp33.mm"
include "eqtr4d.mm"

theorem cdleml1N
  let cB: class B
  let cR: class R
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  assume cdleml1.b: |- B = ( Base ` K )
  assume cdleml1.h: |- H = ( LHyp ` K )
  assume cdleml1.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdleml1.r: |- R = ( ( trL ` K ) ` W )
  assume cdleml1.e: |- E = ( ( TEndo ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. E /\ V e. E /\ f e. T ) /\ ( f =/= ( _I |` B ) /\ ( U ` f ) =/= ( _I |` B ) /\ ( V ` f ) =/= ( _I |` B ) ) ) -> ( R ` ( U ` f ) ) = ( R ` ( V ` f ) ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cU
    cE
    wcel
    #
    cV
    cE
    wcel
    #
    vf
    cv
    #
    cT
    wcel
    #
    w3a
    #
    @5
    cid
    cB
    cres
    #
    wne
    #
    @5
    cU
    cfv
    #
    @8
    wne
    #
    @5
    cV
    cfv
    #
    @8
    wne
    #
    w3a
    #
    w3a
    #
    @10
    cR
    cfv
    #
    @5
    cR
    cfv
    #
    @12
    cR
    cfv
    #
    @15
    @16
    @17
    cK
    cple
    cfv
    #
    wbr
    #
    @16
    @17
    wceq
    #
    @15
    @2
    @3
    @6
    @20
    @2
    @7
    @14
    simp1
    #
    @2
    @3
    @4
    @6
    @14
    simp21
    #
    @2
    @3
    @4
    @6
    @14
    simp23
    #
    cR
    cU
    cT
    cE
    @5
    cH
    cK
    @19
    chlt
    cW
    @19
    eqid
    #
    cdleml1.h
    cdleml1.t
    cdleml1.r
    cdleml1.e
    tendotp
    syl3anc
    @15
    cK
    cal
    wcel
    #
    @16
    cK
    catm
    cfv
    #
    wcel
    #
    @17
    @27
    wcel
    #
    @20
    @21
    wb
    @15
    @0
    @26
    @0
    @1
    @7
    @14
    simp1l
    cK
    hlatl
    syl
    #
    @15
    @2
    @10
    cT
    wcel
    #
    @11
    @28
    @22
    @15
    @2
    @3
    @6
    @31
    @22
    @23
    @24
    cU
    cT
    cE
    @5
    cH
    cK
    chlt
    cW
    cdleml1.h
    cdleml1.t
    cdleml1.e
    tendocl
    syl3anc
    @2
    @7
    @9
    @11
    @13
    simp32
    @27
    cB
    cR
    cT
    @10
    cH
    cK
    cW
    cdleml1.b
    @27
    eqid
    #
    cdleml1.h
    cdleml1.t
    cdleml1.r
    trlnidat
    syl3anc
    @15
    @2
    @6
    @9
    @29
    @22
    @24
    @2
    @7
    @9
    @11
    @13
    simp31
    @27
    cB
    cR
    cT
    @5
    cH
    cK
    cW
    cdleml1.b
    @32
    cdleml1.h
    cdleml1.t
    cdleml1.r
    trlnidat
    syl3anc
    #
    @27
    @16
    @17
    cK
    @19
    @25
    @32
    atcmp
    syl3anc
    mpbid
    @15
    @18
    @17
    @19
    wbr
    #
    @18
    @17
    wceq
    #
    @15
    @2
    @4
    @6
    @34
    @22
    @2
    @3
    @4
    @6
    @14
    simp22
    #
    @24
    cR
    cV
    cT
    cE
    @5
    cH
    cK
    @19
    chlt
    cW
    @25
    cdleml1.h
    cdleml1.t
    cdleml1.r
    cdleml1.e
    tendotp
    syl3anc
    @15
    @26
    @18
    @27
    wcel
    #
    @29
    @34
    @35
    wb
    @30
    @15
    @2
    @12
    cT
    wcel
    #
    @13
    @37
    @22
    @15
    @2
    @4
    @6
    @38
    @22
    @36
    @24
    cV
    cT
    cE
    @5
    cH
    cK
    chlt
    cW
    cdleml1.h
    cdleml1.t
    cdleml1.e
    tendocl
    syl3anc
    @2
    @7
    @9
    @11
    @13
    simp33
    @27
    cB
    cR
    cT
    @12
    cH
    cK
    cW
    cdleml1.b
    @32
    cdleml1.h
    cdleml1.t
    cdleml1.r
    trlnidat
    syl3anc
    @33
    @27
    @18
    @17
    cK
    @19
    @25
    @32
    atcmp
    syl3anc
    mpbid
    eqtr4d
end
