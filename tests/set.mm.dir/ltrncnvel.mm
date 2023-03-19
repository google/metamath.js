include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "ccnv.mm"
include "cfv.mm"
include "ltrncnvat.mm"
include "3adant3r.mm"
include "simp3r.mm"
include "cbs.mm"
include "wb.mm"
include "simp1.mm"
include "simp2.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "ltrnle.mm"
include "syl112anc.mm"
include "wf1o.mm"
include "wceq.mm"
include "ltrn1o.mm"
include "3adant3.mm"
include "simp3l.mm"
include "f1ocnvfv2.mm"
include "syl2anc.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "latref.mm"
include "ltrnval1.mm"
include "breq12d.mm"
include "bitrd.mm"
include "mtbird.mm"
include "jca.mm"

theorem ltrncnvel
  let cA: class A
  let cP: class P
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume ltrnel.l: |- .<_ = ( le ` K )
  assume ltrnel.a: |- A = ( Atoms ` K )
  assume ltrnel.h: |- H = ( LHyp ` K )
  assume ltrnel.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ ( P e. A /\ -. P .<_ W ) ) -> ( ( `' F ` P ) e. A /\ -. ( `' F ` P ) .<_ W ) )

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
    cF
    cT
    wcel
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    w3a
    #
    cP
    cF
    ccnv
    cfv
    #
    cA
    wcel
    #
    @9
    cW
    c.le
    wbr
    #
    wn
    @2
    @3
    @4
    @10
    @6
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    ltrnel.l
    ltrnel.a
    ltrnel.h
    ltrnel.t
    ltrncnvat
    3adant3r
    #
    @8
    @11
    @5
    @2
    @3
    @4
    @6
    simp3r
    @8
    @11
    @9
    cF
    cfv
    #
    cW
    cF
    cfv
    #
    c.le
    wbr
    #
    @5
    @8
    @2
    @3
    @9
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @16
    wcel
    #
    @11
    @15
    wb
    @2
    @3
    @7
    simp1
    #
    @2
    @3
    @7
    simp2
    #
    @8
    @10
    @17
    @12
    cA
    @16
    @9
    cK
    @16
    eqid
    #
    ltrnel.a
    atbase
    syl
    @8
    @1
    @18
    @0
    @1
    @3
    @7
    simp1r
    @16
    cH
    cK
    cW
    @21
    ltrnel.h
    lhpbase
    syl
    #
    @16
    cT
    cF
    cH
    cK
    c.le
    chlt
    cW
    @9
    cW
    @21
    ltrnel.l
    ltrnel.h
    ltrnel.t
    ltrnle
    syl112anc
    @8
    @13
    cP
    @14
    cW
    c.le
    @8
    @16
    @16
    cF
    wf1o
    #
    cP
    @16
    wcel
    #
    @13
    cP
    wceq
    @2
    @3
    @23
    @7
    @16
    cT
    cF
    cH
    cK
    chlt
    cW
    @21
    ltrnel.h
    ltrnel.t
    ltrn1o
    3adant3
    @8
    @4
    @24
    @2
    @3
    @4
    @6
    simp3l
    cA
    @16
    cP
    cK
    @21
    ltrnel.a
    atbase
    syl
    @16
    @16
    cP
    cF
    f1ocnvfv2
    syl2anc
    @8
    @2
    @3
    @18
    cW
    cW
    c.le
    wbr
    #
    @14
    cW
    wceq
    @19
    @20
    @22
    @8
    cK
    clat
    wcel
    #
    @18
    @25
    @8
    @0
    @26
    @0
    @1
    @3
    @7
    simp1l
    cK
    hllat
    syl
    @22
    @16
    cK
    c.le
    cW
    @21
    ltrnel.l
    latref
    syl2anc
    @16
    cT
    cF
    cH
    cK
    c.le
    chlt
    cW
    cW
    @21
    ltrnel.l
    ltrnel.h
    ltrnel.t
    ltrnval1
    syl112anc
    breq12d
    bitrd
    mtbird
    jca
end
