include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "ccnv.mm"
include "ccom.mm"
include "co.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2r.mm"
include "simp2l.mm"
include "ltrncnv.mm"
include "syl2anc.mm"
include "ltrnco.mm"
include "syl3anc.mm"
include "ltrnel.mm"
include "3adant2r.mm"
include "trljat3.mm"
include "simp3l.mm"
include "ltrncoval.mm"
include "syl121anc.mm"
include "coass.mm"
include "cid.mm"
include "cres.mm"
include "wf1o.mm"
include "ltrn1o.mm"
include "f1ococnv1.mm"
include "syl.mm"
include "coeq2d.mm"
include "wf.mm"
include "f1of.mm"
include "fcoi1.mm"
include "3syl.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "eqtr2d.mm"

theorem cdlemk2
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume cdlemk.b: |- B = ( Base ` K )
  assume cdlemk.l: |- .<_ = ( le ` K )
  assume cdlemk.j: |- .\/ = ( join ` K )
  assume cdlemk.a: |- A = ( Atoms ` K )
  assume cdlemk.h: |- H = ( LHyp ` K )
  assume cdlemk.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( ( G ` P ) .\/ ( R ` ( G o. `' F ) ) ) = ( ( F ` P ) .\/ ( R ` ( G o. `' F ) ) ) )

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
    cF
    cfv
    #
    cG
    cF
    ccnv
    #
    ccom
    #
    cR
    cfv
    #
    c.or
    co
    #
    @8
    @10
    cfv
    #
    @11
    c.or
    co
    #
    cP
    cG
    cfv
    #
    @11
    c.or
    co
    @7
    @0
    @10
    cT
    wcel
    #
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
    @12
    @14
    wceq
    @0
    @3
    @6
    simp1
    #
    @7
    @0
    @2
    @9
    cT
    wcel
    #
    @16
    @18
    @0
    @1
    @2
    @6
    simp2r
    #
    @7
    @0
    @1
    @19
    @18
    @0
    @1
    @2
    @6
    simp2l
    #
    cT
    cF
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    ltrncnv
    syl2anc
    cT
    cG
    @9
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    ltrnco
    syl3anc
    #
    @0
    @1
    @6
    @17
    @2
    cA
    cP
    cT
    cF
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
    @10
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
    trljat3
    syl3anc
    @7
    @13
    @15
    @11
    c.or
    @7
    cP
    @10
    cF
    ccom
    #
    cfv
    #
    @13
    @15
    @7
    @0
    @16
    @1
    @4
    @24
    @13
    wceq
    @18
    @22
    @21
    @0
    @3
    @4
    @5
    simp3l
    cA
    cP
    cT
    @10
    cF
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
    @7
    cP
    @23
    cG
    @7
    @23
    cG
    @9
    cF
    ccom
    #
    ccom
    #
    cG
    cG
    @9
    cF
    coass
    @7
    @26
    cG
    cid
    cB
    cres
    #
    ccom
    #
    cG
    @7
    @25
    @27
    cG
    @7
    cB
    cB
    cF
    wf1o
    #
    @25
    @27
    wceq
    @7
    @0
    @1
    @29
    @18
    @21
    cB
    cT
    cF
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
    cF
    f1ococnv1
    syl
    coeq2d
    @7
    cB
    cB
    cG
    wf1o
    #
    cB
    cB
    cG
    wf
    @28
    cG
    wceq
    @7
    @0
    @2
    @30
    @18
    @20
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
    f1of
    cB
    cB
    cG
    fcoi1
    3syl
    eqtrd
    syl5eq
    fveq1d
    eqtr3d
    oveq1d
    eqtr2d
end
