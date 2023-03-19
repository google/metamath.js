include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "ccnv.mm"
include "ccom.mm"
include "simp11.mm"
include "simp2l.mm"
include "simp12.mm"
include "ltrnco.mm"
include "syl3anc.mm"
include "simp13.mm"
include "simp3.mm"
include "cdlemg46.mm"
include "syl121anc.mm"
include "simp2r.mm"
include "neeqtrd.mm"
include "cdlemg44.mm"
include "coass.mm"
include "syl6eqr.mm"
include "simp33.mm"
include "coeq1d.mm"
include "eqtr4d.mm"
include "3eqtr3g.mm"
include "coeq2d.mm"
include "wf1o.mm"
include "ltrn1o.mm"
include "syl2anc.mm"
include "f1ococnv1.mm"
include "syl.mm"
include "syl5eqr.mm"
include "wf.mm"
include "f1of.mm"
include "fcoi2.mm"
include "3syl.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"

theorem cdlemg47
  let cB: class B
  let cR: class R
  let cT: class T
  let vh: setvar h
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  assume cdlemg46.b: |- B = ( Base ` K )
  assume cdlemg46.h: |- H = ( LHyp ` K )
  assume cdlemg46.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg46.r: |- R = ( ( trL ` K ) ` W )

  disjoint F h
  disjoint H h
  disjoint K h
  disjoint R h
  disjoint T h
  disjoint W h
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) /\ ( h e. T /\ ( R ` F ) = ( R ` G ) ) /\ ( F =/= ( _I |` B ) /\ h =/= ( _I |` B ) /\ ( R ` h ) =/= ( R ` F ) ) ) -> ( F o. G ) = ( G o. F ) )

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
    vh
    cv
    #
    cT
    wcel
    #
    cF
    cR
    cfv
    #
    cG
    cR
    cfv
    #
    wceq
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
    @4
    @10
    wne
    #
    @4
    cR
    cfv
    #
    @6
    wne
    #
    w3a
    #
    w3a
    #
    @4
    ccnv
    #
    @4
    cF
    cG
    ccom
    #
    ccom
    #
    ccom
    #
    @17
    @4
    cG
    cF
    ccom
    #
    ccom
    #
    ccom
    #
    @18
    @21
    @16
    @19
    @22
    @17
    @16
    @4
    cF
    ccom
    #
    cG
    ccom
    #
    @4
    cG
    ccom
    #
    cF
    ccom
    #
    @19
    @22
    @16
    @25
    cG
    @4
    ccom
    #
    cF
    ccom
    #
    @27
    @16
    @25
    cG
    @24
    ccom
    #
    @29
    @16
    @0
    @24
    cT
    wcel
    #
    @2
    @24
    cR
    cfv
    #
    @7
    wne
    @25
    @30
    wceq
    @0
    @1
    @2
    @9
    @15
    simp11
    #
    @16
    @0
    @5
    @1
    @31
    @33
    @3
    @5
    @8
    @15
    simp2l
    #
    @0
    @1
    @2
    @9
    @15
    simp12
    #
    cT
    @4
    cF
    cH
    cK
    cW
    cdlemg46.h
    cdlemg46.t
    ltrnco
    syl3anc
    @0
    @1
    @2
    @9
    @15
    simp13
    #
    @16
    @32
    @6
    @7
    @16
    @0
    @1
    @5
    @15
    @32
    @6
    wne
    @33
    @35
    @34
    @3
    @9
    @15
    simp3
    cB
    cR
    cT
    vh
    cF
    cH
    cK
    cW
    cdlemg46.b
    cdlemg46.h
    cdlemg46.t
    cdlemg46.r
    cdlemg46
    syl121anc
    @3
    @5
    @8
    @15
    simp2r
    #
    neeqtrd
    cR
    cT
    @24
    cG
    cH
    cK
    cW
    cdlemg46.h
    cdlemg46.t
    cdlemg46.r
    cdlemg44
    syl121anc
    cG
    @4
    cF
    coass
    syl6eqr
    @16
    @26
    @28
    cF
    @16
    @0
    @5
    @2
    @13
    @7
    wne
    @26
    @28
    wceq
    @33
    @34
    @36
    @16
    @13
    @6
    @7
    @3
    @9
    @11
    @12
    @14
    simp33
    @37
    neeqtrd
    cR
    cT
    @4
    cG
    cH
    cK
    cW
    cdlemg46.h
    cdlemg46.t
    cdlemg46.r
    cdlemg44
    syl121anc
    coeq1d
    eqtr4d
    @4
    cF
    cG
    coass
    @4
    cG
    cF
    coass
    3eqtr3g
    coeq2d
    @16
    @20
    @10
    @18
    ccom
    #
    @18
    @16
    @20
    @17
    @4
    ccom
    #
    @18
    ccom
    @38
    @17
    @4
    @18
    coass
    @16
    @39
    @10
    @18
    @16
    cB
    cB
    @4
    wf1o
    #
    @39
    @10
    wceq
    @16
    @0
    @5
    @40
    @33
    @34
    cB
    cT
    @4
    cH
    cK
    chlt
    cW
    cdlemg46.b
    cdlemg46.h
    cdlemg46.t
    ltrn1o
    syl2anc
    cB
    cB
    @4
    f1ococnv1
    syl
    #
    coeq1d
    syl5eqr
    @16
    cB
    cB
    @18
    wf1o
    #
    cB
    cB
    @18
    wf
    @38
    @18
    wceq
    @16
    @0
    @18
    cT
    wcel
    #
    @42
    @33
    @16
    @0
    @1
    @2
    @43
    @33
    @35
    @36
    cT
    cF
    cG
    cH
    cK
    cW
    cdlemg46.h
    cdlemg46.t
    ltrnco
    syl3anc
    cB
    cT
    @18
    cH
    cK
    chlt
    cW
    cdlemg46.b
    cdlemg46.h
    cdlemg46.t
    ltrn1o
    syl2anc
    cB
    cB
    @18
    f1of
    cB
    cB
    @18
    fcoi2
    3syl
    eqtrd
    @16
    @23
    @10
    @21
    ccom
    #
    @21
    @16
    @23
    @39
    @21
    ccom
    @44
    @17
    @4
    @21
    coass
    @16
    @39
    @10
    @21
    @41
    coeq1d
    syl5eqr
    @16
    cB
    cB
    @21
    wf1o
    #
    cB
    cB
    @21
    wf
    @44
    @21
    wceq
    @16
    @0
    @21
    cT
    wcel
    #
    @45
    @33
    @16
    @0
    @2
    @1
    @46
    @33
    @36
    @35
    cT
    cG
    cF
    cH
    cK
    cW
    cdlemg46.h
    cdlemg46.t
    ltrnco
    syl3anc
    cB
    cT
    @21
    cH
    cK
    chlt
    cW
    cdlemg46.b
    cdlemg46.h
    cdlemg46.t
    ltrn1o
    syl2anc
    cB
    cB
    @21
    f1of
    cB
    cB
    @21
    fcoi2
    3syl
    eqtrd
    3eqtr3d
end
