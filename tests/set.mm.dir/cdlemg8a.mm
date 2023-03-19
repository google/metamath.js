include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "co.mm"
include "cp0.mm"
include "simp1.mm"
include "simp2r.mm"
include "eqid.mm"
include "lhpmat.mm"
include "syl2anc.mm"
include "cdlemg6.mm"
include "oveq2d.mm"
include "simp1l.mm"
include "simp2rl.mm"
include "hlatjidm.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "simp33.mm"
include "simp2ll.mm"
include "simp2l.mm"
include "3eqtr4rd.mm"

theorem cdlemg8a
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemg8.l: |- .<_ = ( le ` K )
  assume cdlemg8.j: |- .\/ = ( join ` K )
  assume cdlemg8.m: |- ./\ = ( meet ` K )
  assume cdlemg8.a: |- A = ( Atoms ` K )
  assume cdlemg8.h: |- H = ( LHyp ` K )
  assume cdlemg8.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ ( F ` ( G ` P ) ) = P ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) )

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
    cQ
    cA
    wcel
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
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
    cP
    cG
    cfv
    cF
    cfv
    #
    cP
    wceq
    #
    w3a
    #
    w3a
    #
    cQ
    cW
    c.an
    co
    #
    cK
    cp0
    cfv
    #
    cQ
    cQ
    cG
    cfv
    cF
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    cP
    @12
    c.or
    co
    #
    cW
    c.an
    co
    #
    @15
    @2
    @8
    @16
    @17
    wceq
    @2
    @9
    @14
    simp1
    #
    @2
    @5
    @8
    @14
    simp2r
    cA
    cQ
    cH
    cK
    c.le
    c.an
    cW
    @17
    cdlemg8.l
    cdlemg8.m
    @17
    eqid
    #
    cdlemg8.a
    cdlemg8.h
    lhpmat
    syl2anc
    @15
    @19
    cQ
    cW
    c.an
    @15
    @19
    cQ
    cQ
    c.or
    co
    #
    cQ
    @15
    @18
    cQ
    cQ
    c.or
    cA
    cP
    cQ
    cT
    cF
    cG
    cH
    cK
    c.le
    cW
    cdlemg8.l
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    cdlemg6
    oveq2d
    @15
    @0
    @6
    @24
    cQ
    wceq
    @0
    @1
    @9
    @14
    simp1l
    #
    @6
    @7
    @5
    @2
    @14
    simp2rl
    cA
    c.or
    cK
    cQ
    cdlemg8.j
    cdlemg8.a
    hlatjidm
    syl2anc
    eqtrd
    oveq1d
    @15
    @21
    cP
    cW
    c.an
    co
    #
    @17
    @15
    @20
    cP
    cW
    c.an
    @15
    @20
    cP
    cP
    c.or
    co
    #
    cP
    @15
    @12
    cP
    cP
    c.or
    @2
    @9
    @10
    @11
    @13
    simp33
    oveq2d
    @15
    @0
    @3
    @27
    cP
    wceq
    @25
    @3
    @4
    @8
    @2
    @14
    simp2ll
    cA
    c.or
    cK
    cP
    cdlemg8.j
    cdlemg8.a
    hlatjidm
    syl2anc
    eqtrd
    oveq1d
    @15
    @2
    @5
    @26
    @17
    wceq
    @22
    @2
    @5
    @8
    @14
    simp2l
    cA
    cP
    cH
    cK
    c.le
    c.an
    cW
    @17
    cdlemg8.l
    cdlemg8.m
    @23
    cdlemg8.a
    cdlemg8.h
    lhpmat
    syl2anc
    eqtrd
    3eqtr4rd
end
