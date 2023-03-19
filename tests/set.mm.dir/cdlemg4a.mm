include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "cjn.mm"
include "co.mm"
include "cmee.mm"
include "simp3.mm"
include "oveq2d.mm"
include "simp1l.mm"
include "simp1.mm"
include "simp23.mm"
include "simp21.mm"
include "ltrnel.mm"
include "simpld.mm"
include "syl3anc.mm"
include "simp21l.mm"
include "eqid.mm"
include "hlatjcom.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "simp22.mm"
include "trlval2.mm"
include "3eqtr4d.mm"

theorem cdlemg4a
  let cA: class A
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vr: setvar r
  let c.or: class .\/
  let cQ: class Q
  let cV: class V
  assume cdlemg4.l: |- .<_ = ( le ` K )
  assume cdlemg4.a: |- A = ( Atoms ` K )
  assume cdlemg4.h: |- H = ( LHyp ` K )
  assume cdlemg4.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg4.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ F e. T /\ G e. T ) /\ ( F ` ( G ` P ) ) = P ) -> ( R ` F ) = ( R ` G ) )

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
    cP
    cG
    cfv
    #
    cF
    cfv
    #
    cP
    wceq
    #
    w3a
    #
    @9
    @10
    cK
    cjn
    cfv
    #
    co
    #
    cW
    cK
    cmee
    cfv
    #
    co
    #
    cP
    @9
    @13
    co
    #
    cW
    @15
    co
    #
    cF
    cR
    cfv
    #
    cG
    cR
    cfv
    #
    @12
    @14
    @17
    cW
    @15
    @12
    @14
    @9
    cP
    @13
    co
    #
    @17
    @12
    @10
    cP
    @9
    @13
    @2
    @8
    @11
    simp3
    oveq2d
    @12
    @0
    @9
    cA
    wcel
    #
    @3
    @21
    @17
    wceq
    @0
    @1
    @8
    @11
    simp1l
    @12
    @2
    @7
    @5
    @22
    @2
    @8
    @11
    simp1
    #
    @2
    @5
    @6
    @7
    @11
    simp23
    #
    @2
    @5
    @6
    @7
    @11
    simp21
    #
    @2
    @7
    @5
    w3a
    @22
    @9
    cW
    c.le
    wbr
    wn
    #
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg4.l
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    ltrnel
    #
    simpld
    syl3anc
    @3
    @4
    @6
    @7
    @2
    @11
    simp21l
    cA
    @13
    cK
    @9
    cP
    @13
    eqid
    #
    cdlemg4.a
    hlatjcom
    syl3anc
    eqtrd
    oveq1d
    @12
    @2
    @6
    @22
    @26
    wa
    #
    @19
    @16
    wceq
    @23
    @2
    @5
    @6
    @7
    @11
    simp22
    @12
    @2
    @7
    @5
    @29
    @23
    @24
    @25
    @27
    syl3anc
    cA
    @9
    cR
    cT
    cF
    cH
    @13
    cK
    c.le
    @15
    cW
    cdlemg4.l
    @28
    @15
    eqid
    #
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    cdlemg4.r
    trlval2
    syl3anc
    @12
    @2
    @7
    @5
    @20
    @18
    wceq
    @23
    @24
    @25
    cA
    cP
    cR
    cT
    cG
    cH
    @13
    cK
    c.le
    @15
    cW
    cdlemg4.l
    @28
    @30
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    cdlemg4.r
    trlval2
    syl3anc
    3eqtr4d
end
