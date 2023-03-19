include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "ccnv.mm"
include "ccom.mm"
include "cid.mm"
include "cbs.mm"
include "cres.mm"
include "wf1o.mm"
include "wceq.mm"
include "simp1.mm"
include "tendocl.mm"
include "eqid.mm"
include "ltrn1o.mm"
include "syl2anc.mm"
include "f1ococnv1.mm"
include "syl.mm"
include "coeq1d.mm"
include "simp2.mm"
include "tendoid.mm"
include "3adant2.mm"
include "f1ococnv2.mm"
include "fveq2d.mm"
include "3eqtr4rd.mm"
include "simp3.mm"
include "ltrncnv.mm"
include "tendospdi1.mm"
include "syl13anc.mm"
include "eqtrd.mm"
include "coeq2d.mm"
include "coass.mm"
include "3eqtr4g.mm"
include "wf.mm"
include "syld3an3.mm"
include "f1of.mm"
include "fcoi2.mm"
include "3syl.mm"
include "3eqtrd.mm"
include "3eqtr3rd.mm"

theorem tendocnv
  let cS: class S
  let cT: class T
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  assume tendosp.h: |- H = ( LHyp ` K )
  assume tendosp.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendosp.e: |- E = ( ( TEndo ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ S e. E /\ F e. T ) -> `' ( S ` F ) = ( S ` `' F ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cS
    cE
    wcel
    #
    cF
    cT
    wcel
    #
    w3a
    #
    cF
    cS
    cfv
    #
    ccnv
    #
    @4
    ccom
    #
    @5
    ccom
    #
    cid
    cK
    cbs
    cfv
    #
    cres
    #
    @5
    ccom
    #
    cF
    ccnv
    #
    cS
    cfv
    #
    @5
    @3
    @6
    @9
    @5
    @3
    @8
    @8
    @4
    wf1o
    #
    @6
    @9
    wceq
    @3
    @0
    @4
    cT
    wcel
    #
    @13
    @0
    @1
    @2
    simp1
    #
    cS
    cT
    cE
    cF
    cH
    cK
    chlt
    cW
    tendosp.h
    tendosp.t
    tendosp.e
    tendocl
    #
    @8
    cT
    @4
    cH
    cK
    chlt
    cW
    @8
    eqid
    #
    tendosp.h
    tendosp.t
    ltrn1o
    syl2anc
    #
    @8
    @8
    @4
    f1ococnv1
    syl
    #
    coeq1d
    @3
    @7
    @6
    @12
    ccom
    #
    @9
    @12
    ccom
    #
    @12
    @3
    @5
    @4
    @5
    ccom
    #
    ccom
    @5
    @4
    @12
    ccom
    #
    ccom
    @7
    @20
    @3
    @22
    @23
    @5
    @3
    @22
    cF
    @11
    ccom
    #
    cS
    cfv
    #
    @23
    @3
    @9
    cS
    cfv
    #
    @9
    @25
    @22
    @3
    @0
    @1
    @26
    @9
    wceq
    @15
    @0
    @1
    @2
    simp2
    #
    @8
    cS
    cE
    cH
    cK
    cW
    @17
    tendosp.h
    tendosp.e
    tendoid
    syl2anc
    @3
    @24
    @9
    cS
    @3
    @8
    @8
    cF
    wf1o
    #
    @24
    @9
    wceq
    @0
    @2
    @28
    @1
    @8
    cT
    cF
    cH
    cK
    chlt
    cW
    @17
    tendosp.h
    tendosp.t
    ltrn1o
    3adant2
    @8
    @8
    cF
    f1ococnv2
    syl
    fveq2d
    @3
    @13
    @22
    @9
    wceq
    @18
    @8
    @8
    @4
    f1ococnv2
    syl
    3eqtr4rd
    @3
    @0
    @1
    @2
    @11
    cT
    wcel
    #
    @25
    @23
    wceq
    @15
    @27
    @0
    @1
    @2
    simp3
    @0
    @2
    @29
    @1
    cT
    cF
    cH
    cK
    cW
    tendosp.h
    tendosp.t
    ltrncnv
    3adant2
    #
    cT
    cS
    cE
    cF
    @11
    cH
    cK
    chlt
    cW
    tendosp.h
    tendosp.t
    tendosp.e
    tendospdi1
    syl13anc
    eqtrd
    coeq2d
    @5
    @4
    @5
    coass
    @5
    @4
    @12
    coass
    3eqtr4g
    @3
    @6
    @9
    @12
    @19
    coeq1d
    @3
    @8
    @8
    @12
    wf1o
    #
    @8
    @8
    @12
    wf
    @21
    @12
    wceq
    @3
    @0
    @12
    cT
    wcel
    #
    @31
    @15
    @0
    @1
    @2
    @29
    @32
    @30
    cS
    cT
    cE
    @11
    cH
    cK
    chlt
    cW
    tendosp.h
    tendosp.t
    tendosp.e
    tendocl
    syld3an3
    @8
    cT
    @12
    cH
    cK
    chlt
    cW
    @17
    tendosp.h
    tendosp.t
    ltrn1o
    syl2anc
    @8
    @8
    @12
    f1of
    @8
    @8
    @12
    fcoi2
    3syl
    3eqtrd
    @3
    @8
    @8
    @5
    wf1o
    #
    @8
    @8
    @5
    wf
    @10
    @5
    wceq
    @3
    @0
    @5
    cT
    wcel
    #
    @33
    @15
    @3
    @0
    @14
    @34
    @15
    @16
    cT
    @4
    cH
    cK
    cW
    tendosp.h
    tendosp.t
    ltrncnv
    syl2anc
    @8
    cT
    @5
    cH
    cK
    chlt
    cW
    @17
    tendosp.h
    tendosp.t
    ltrn1o
    syl2anc
    @8
    @8
    @5
    f1of
    @8
    @8
    @5
    fcoi2
    3syl
    3eqtr3rd
end
