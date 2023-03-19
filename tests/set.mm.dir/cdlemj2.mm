include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "catm.mm"
include "wral.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "simpr.mm"
include "eqid.mm"
include "cdlemj1.mm"
include "syl113anc.mm"
include "exp32.mm"
include "ralrimiv.mm"
include "wb.mm"
include "simp11.mm"
include "simp121.mm"
include "simp133.mm"
include "tendocl.mm"
include "syl3anc.mm"
include "simp122.mm"
include "ltrneq.mm"
include "mpbid.mm"

theorem cdlemj2
  let cB: class B
  let cR: class R
  let cT: class T
  let cU: class U
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vp: setvar p
  assume cdlemj.b: |- B = ( Base ` K )
  assume cdlemj.h: |- H = ( LHyp ` K )
  assume cdlemj.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemj.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemj.e: |- E = ( ( TEndo ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( U e. E /\ V e. E /\ ( U ` F ) = ( V ` F ) ) /\ ( F e. T /\ F =/= ( _I |` B ) /\ h e. T ) ) /\ ( h =/= ( _I |` B ) /\ g e. T /\ g =/= ( _I |` B ) ) /\ ( ( R ` F ) =/= ( R ` g ) /\ ( R ` g ) =/= ( R ` h ) ) ) -> ( U ` h ) = ( V ` h ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    cF
    cU
    cfv
    cF
    cV
    cfv
    wceq
    #
    w3a
    #
    cF
    cT
    wcel
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    vh
    cv
    #
    cT
    wcel
    #
    w3a
    #
    w3a
    #
    @8
    @6
    wne
    vg
    cv
    #
    cT
    wcel
    @12
    @6
    wne
    w3a
    #
    cF
    cR
    cfv
    @12
    cR
    cfv
    #
    wne
    #
    @14
    @8
    cR
    cfv
    wne
    #
    wa
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
    @19
    @8
    cU
    cfv
    #
    cfv
    @19
    @8
    cV
    cfv
    #
    cfv
    wceq
    #
    wi
    #
    vp
    cK
    catm
    cfv
    #
    wral
    #
    @22
    @23
    wceq
    #
    @18
    @25
    vp
    @26
    @18
    @19
    @26
    wcel
    #
    @21
    @24
    @18
    @29
    @21
    wa
    #
    wa
    @11
    @13
    @15
    @16
    @30
    @24
    @11
    @13
    @17
    @30
    simpl1
    @11
    @13
    @17
    @30
    simpl2
    @15
    @16
    @11
    @13
    @30
    simpl3l
    @15
    @16
    @11
    @13
    @30
    simpl3r
    @18
    @30
    simpr
    @26
    cB
    cR
    cT
    cU
    vg
    vh
    cE
    cF
    cH
    cK
    @20
    cV
    cW
    vp
    cdlemj.b
    cdlemj.h
    cdlemj.t
    cdlemj.r
    cdlemj.e
    @20
    eqid
    #
    @26
    eqid
    #
    cdlemj1
    syl113anc
    exp32
    ralrimiv
    @18
    @0
    @22
    cT
    wcel
    #
    @23
    cT
    wcel
    #
    @27
    @28
    wb
    @0
    @4
    @10
    @13
    @17
    simp11
    #
    @18
    @0
    @1
    @9
    @33
    @35
    @1
    @2
    @3
    @0
    @10
    @13
    @17
    simp121
    @5
    @7
    @9
    @0
    @4
    @13
    @17
    simp133
    #
    cU
    cT
    cE
    @8
    cH
    cK
    chlt
    cW
    cdlemj.h
    cdlemj.t
    cdlemj.e
    tendocl
    syl3anc
    @18
    @0
    @2
    @9
    @34
    @35
    @1
    @2
    @3
    @0
    @10
    @13
    @17
    simp122
    @36
    cV
    cT
    cE
    @8
    cH
    cK
    chlt
    cW
    cdlemj.h
    cdlemj.t
    cdlemj.e
    tendocl
    syl3anc
    @26
    cT
    @22
    @23
    cH
    cK
    @20
    cW
    vp
    @31
    @32
    cdlemj.h
    cdlemj.t
    ltrneq
    syl3anc
    mpbid
end
