include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "coass.mm"
include "cid.mm"
include "cres.mm"
include "wf1o.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2l.mm"
include "ltrn1o.mm"
include "syl2anc.mm"
include "f1ococnv1.mm"
include "syl.mm"
include "coeq2d.mm"
include "wf.mm"
include "simp2r.mm"
include "f1of.mm"
include "fcoi1.mm"
include "3syl.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "ltrncnv.mm"
include "ltrnco.mm"
include "syl3anc.mm"
include "simp3l.mm"
include "ltrncoval.mm"
include "syl121anc.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "ltrnel.mm"
include "3adant2r.mm"
include "trljat1.mm"
include "eqtr4d.mm"

theorem cdlemk8
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  assume cdlemk.b: |- B = ( Base ` K )
  assume cdlemk.l: |- .<_ = ( le ` K )
  assume cdlemk.j: |- .\/ = ( join ` K )
  assume cdlemk.a: |- A = ( Atoms ` K )
  assume cdlemk.h: |- H = ( LHyp ` K )
  assume cdlemk.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk.m: |- ./\ = ( meet ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( G e. T /\ X e. T ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( ( G ` P ) .\/ ( X ` P ) ) = ( ( G ` P ) .\/ ( R ` ( X o. `' G ) ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cG
    cT
    wcel
    #
    cX
    cT
    wcel
    #
    wa
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cP
    cG
    cfv
    #
    cP
    cX
    cfv
    #
    c.or
    co
    @8
    @8
    cX
    cG
    ccnv
    #
    ccom
    #
    cfv
    #
    c.or
    co
    #
    @8
    @11
    cR
    cfv
    c.or
    co
    #
    @7
    @9
    @12
    @8
    c.or
    @7
    cP
    @11
    cG
    ccom
    #
    cfv
    #
    @9
    @12
    @7
    cP
    @15
    cX
    @7
    @15
    cX
    @10
    cG
    ccom
    #
    ccom
    #
    cX
    cX
    @10
    cG
    coass
    @7
    @18
    cX
    cid
    cB
    cres
    #
    ccom
    #
    cX
    @7
    @17
    @19
    cX
    @7
    cB
    cB
    cG
    wf1o
    #
    @17
    @19
    wceq
    @7
    @0
    @1
    @21
    @0
    @3
    @6
    simp1
    #
    @0
    @1
    @2
    @6
    simp2l
    #
    cB
    cT
    cG
    cH
    cK
    chlt
    cW
    cdlemk.b
    cdlemk.h
    cdlemk.t
    ltrn1o
    syl2anc
    cB
    cB
    cG
    f1ococnv1
    syl
    coeq2d
    @7
    cB
    cB
    cX
    wf1o
    #
    cB
    cB
    cX
    wf
    @20
    cX
    wceq
    @7
    @0
    @2
    @24
    @22
    @0
    @1
    @2
    @6
    simp2r
    #
    cB
    cT
    cX
    cH
    cK
    chlt
    cW
    cdlemk.b
    cdlemk.h
    cdlemk.t
    ltrn1o
    syl2anc
    cB
    cB
    cX
    f1of
    cB
    cB
    cX
    fcoi1
    3syl
    eqtrd
    syl5eq
    fveq1d
    @7
    @0
    @11
    cT
    wcel
    #
    @1
    @4
    @16
    @12
    wceq
    @22
    @7
    @0
    @2
    @10
    cT
    wcel
    #
    @26
    @22
    @25
    @7
    @0
    @1
    @27
    @22
    @23
    cT
    cG
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    ltrncnv
    syl2anc
    cT
    cX
    @10
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    ltrnco
    syl3anc
    #
    @23
    @0
    @3
    @4
    @5
    simp3l
    cA
    cP
    cT
    @11
    cG
    cH
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.a
    cdlemk.h
    cdlemk.t
    ltrncoval
    syl121anc
    eqtr3d
    oveq2d
    @7
    @0
    @26
    @8
    cA
    wcel
    @8
    cW
    c.le
    wbr
    wn
    wa
    #
    @14
    @13
    wceq
    @22
    @28
    @0
    @1
    @6
    @29
    @2
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.a
    cdlemk.h
    cdlemk.t
    ltrnel
    3adant2r
    cA
    @8
    cR
    cT
    @11
    cH
    c.or
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.j
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trljat1
    syl3anc
    eqtr4d
end
