include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wne.mm"
include "ccom.mm"
include "cp0.mm"
include "wceq.mm"
include "cid.mm"
include "cbs.mm"
include "cres.mm"
include "wb.mm"
include "ltrnco.mm"
include "3expb.mm"
include "eqid.mm"
include "trlid0b.mm"
include "syldan.mm"
include "ccnv.mm"
include "coass.mm"
include "wf1o.mm"
include "simpll.mm"
include "simplrl.mm"
include "ltrn1o.mm"
include "syl2anc.mm"
include "f1ococnv1.mm"
include "syl.mm"
include "coeq1d.mm"
include "coeq2.mm"
include "adantl.mm"
include "3eqtr3a.mm"
include "wf.mm"
include "simplrr.mm"
include "f1of.mm"
include "fcoi2.mm"
include "3syl.mm"
include "ltrncnv.mm"
include "fcoi1.mm"
include "3eqtr3d.mm"
include "fveq2d.mm"
include "trlcnv.mm"
include "eqtr2d.mm"
include "ex.mm"
include "sylbird.mm"
include "necon3d.mm"
include "trlatn0.mm"
include "sylibrd.mm"
include "3impia.mm"

theorem trlcoat
  let cA: class A
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  assume trlcoat.a: |- A = ( Atoms ` K )
  assume trlcoat.h: |- H = ( LHyp ` K )
  assume trlcoat.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlcoat.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ ( R ` F ) =/= ( R ` G ) ) -> ( R ` ( F o. G ) ) e. A )

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
    #
    cG
    cR
    cfv
    #
    wne
    #
    cF
    cG
    ccom
    #
    cR
    cfv
    #
    cA
    wcel
    #
    @0
    @3
    wa
    #
    @6
    @8
    cK
    cp0
    cfv
    #
    wne
    #
    @9
    @10
    @8
    @11
    @4
    @5
    @10
    @8
    @11
    wceq
    #
    @7
    cid
    cK
    cbs
    cfv
    #
    cres
    #
    wceq
    #
    @4
    @5
    wceq
    #
    @0
    @3
    @7
    cT
    wcel
    #
    @16
    @13
    wb
    @0
    @1
    @2
    @18
    cT
    cF
    cG
    cH
    cK
    cW
    trlcoat.h
    trlcoat.t
    ltrnco
    3expb
    #
    @14
    cR
    cT
    @7
    cH
    cK
    cW
    @11
    @14
    eqid
    #
    @11
    eqid
    #
    trlcoat.h
    trlcoat.t
    trlcoat.r
    trlid0b
    syldan
    @10
    @16
    @17
    @10
    @16
    wa
    #
    @5
    cF
    ccnv
    #
    cR
    cfv
    #
    @4
    @22
    cG
    @23
    cR
    @22
    @15
    cG
    ccom
    #
    @23
    @15
    ccom
    #
    cG
    @23
    @22
    @23
    cF
    ccom
    #
    cG
    ccom
    @23
    @7
    ccom
    #
    @25
    @26
    @23
    cF
    cG
    coass
    @22
    @27
    @15
    cG
    @22
    @14
    @14
    cF
    wf1o
    #
    @27
    @15
    wceq
    @22
    @0
    @1
    @29
    @0
    @3
    @16
    simpll
    #
    @0
    @1
    @2
    @16
    simplrl
    #
    @14
    cT
    cF
    cH
    cK
    chlt
    cW
    @20
    trlcoat.h
    trlcoat.t
    ltrn1o
    syl2anc
    @14
    @14
    cF
    f1ococnv1
    syl
    coeq1d
    @16
    @28
    @26
    wceq
    @10
    @7
    @15
    @23
    coeq2
    adantl
    3eqtr3a
    @22
    @14
    @14
    cG
    wf1o
    #
    @14
    @14
    cG
    wf
    @25
    cG
    wceq
    @22
    @0
    @2
    @32
    @30
    @0
    @1
    @2
    @16
    simplrr
    @14
    cT
    cG
    cH
    cK
    chlt
    cW
    @20
    trlcoat.h
    trlcoat.t
    ltrn1o
    syl2anc
    @14
    @14
    cG
    f1of
    @14
    @14
    cG
    fcoi2
    3syl
    @22
    @14
    @14
    @23
    wf1o
    #
    @14
    @14
    @23
    wf
    @26
    @23
    wceq
    @22
    @0
    @23
    cT
    wcel
    #
    @33
    @30
    @22
    @0
    @1
    @34
    @30
    @31
    cT
    cF
    cH
    cK
    cW
    trlcoat.h
    trlcoat.t
    ltrncnv
    syl2anc
    @14
    cT
    @23
    cH
    cK
    chlt
    cW
    @20
    trlcoat.h
    trlcoat.t
    ltrn1o
    syl2anc
    @14
    @14
    @23
    f1of
    @14
    @14
    @23
    fcoi1
    3syl
    3eqtr3d
    fveq2d
    @22
    @0
    @1
    @24
    @4
    wceq
    @30
    @31
    cR
    cT
    cF
    cH
    cK
    cW
    trlcoat.h
    trlcoat.t
    trlcoat.r
    trlcnv
    syl2anc
    eqtr2d
    ex
    sylbird
    necon3d
    @0
    @3
    @18
    @9
    @12
    wb
    @19
    cA
    cR
    cT
    @7
    cH
    cK
    cW
    @11
    @21
    trlcoat.a
    trlcoat.h
    trlcoat.t
    trlcoat.r
    trlatn0
    syldan
    sylibrd
    3impia
end
