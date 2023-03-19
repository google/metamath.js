include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cp0.mm"
include "cfv.mm"
include "ccvr.mm"
include "wbr.mm"
include "simp3.mm"
include "ltrncl.mm"
include "2thd.mm"
include "wb.mm"
include "simp1.mm"
include "simp2.mm"
include "cops.mm"
include "simp1l.mm"
include "hlop.mm"
include "eqid.mm"
include "op0cl.mm"
include "3syl.mm"
include "ltrncvr.mm"
include "syl112anc.mm"
include "cple.mm"
include "wceq.mm"
include "syl.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "op0le.mm"
include "syl2anc.mm"
include "ltrnval1.mm"
include "breq1d.mm"
include "bitrd.mm"
include "anbi12d.mm"
include "isat.mm"
include "3bitr4d.mm"

theorem ltrnatb
  let cA: class A
  let cB: class B
  let cP: class P
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  assume ltrnatb.b: |- B = ( Base ` K )
  assume ltrnatb.a: |- A = ( Atoms ` K )
  assume ltrnatb.h: |- H = ( LHyp ` K )
  assume ltrnatb.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ P e. B ) -> ( P e. A <-> ( F ` P ) e. A ) )

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
    cB
    wcel
    #
    w3a
    #
    @4
    cK
    cp0
    cfv
    #
    cP
    cK
    ccvr
    cfv
    #
    wbr
    #
    wa
    #
    cP
    cF
    cfv
    #
    cB
    wcel
    #
    @6
    @10
    @7
    wbr
    #
    wa
    #
    cP
    cA
    wcel
    #
    @10
    cA
    wcel
    #
    @5
    @4
    @11
    @8
    @12
    @5
    @4
    @11
    @2
    @3
    @4
    simp3
    #
    cB
    cT
    cF
    cH
    cK
    chlt
    cW
    cP
    ltrnatb.b
    ltrnatb.h
    ltrnatb.t
    ltrncl
    2thd
    @5
    @8
    @6
    cF
    cfv
    #
    @10
    @7
    wbr
    #
    @12
    @5
    @2
    @3
    @6
    cB
    wcel
    #
    @4
    @8
    @18
    wb
    @2
    @3
    @4
    simp1
    #
    @2
    @3
    @4
    simp2
    #
    @5
    @0
    cK
    cops
    wcel
    #
    @19
    @0
    @1
    @3
    @4
    simp1l
    #
    cK
    hlop
    #
    cB
    cK
    @6
    ltrnatb.b
    @6
    eqid
    #
    op0cl
    3syl
    #
    @16
    cB
    @7
    cT
    cF
    cH
    cK
    chlt
    cW
    @6
    cP
    ltrnatb.b
    @7
    eqid
    #
    ltrnatb.h
    ltrnatb.t
    ltrncvr
    syl112anc
    @5
    @17
    @6
    @10
    @7
    @5
    @2
    @3
    @19
    @6
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    @17
    @6
    wceq
    @20
    @21
    @26
    @5
    @22
    cW
    cB
    wcel
    #
    @29
    @5
    @0
    @22
    @23
    @24
    syl
    @5
    @1
    @30
    @0
    @1
    @3
    @4
    simp1r
    cB
    cH
    cK
    cW
    ltrnatb.b
    ltrnatb.h
    lhpbase
    syl
    cB
    cK
    @28
    cW
    @6
    ltrnatb.b
    @28
    eqid
    #
    @25
    op0le
    syl2anc
    cB
    cT
    cF
    cH
    cK
    @28
    chlt
    cW
    @6
    ltrnatb.b
    @31
    ltrnatb.h
    ltrnatb.t
    ltrnval1
    syl112anc
    breq1d
    bitrd
    anbi12d
    @5
    @0
    @14
    @9
    wb
    @23
    cA
    cB
    @7
    chlt
    cP
    cK
    @6
    ltrnatb.b
    @25
    @27
    ltrnatb.a
    isat
    syl
    @5
    @0
    @15
    @13
    wb
    @23
    cA
    cB
    @7
    chlt
    @10
    cK
    @6
    ltrnatb.b
    @25
    @27
    ltrnatb.a
    isat
    syl
    3bitr4d
end
