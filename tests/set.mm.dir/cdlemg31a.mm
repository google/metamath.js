include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "clat.mm"
include "cbs.mm"
include "wbr.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2l.mm"
include "simp3l.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp2r.mm"
include "atbase.mm"
include "simp1.mm"
include "simp3r.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "latjcl.mm"
include "latmle1.mm"
include "syl5eqbr.mm"

theorem cdlemg31a
  let vv: setvar v
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let vr: setvar r
  let cG: class G
  let cS: class S
  assume cdlemg12.l: |- .<_ = ( le ` K )
  assume cdlemg12.j: |- .\/ = ( join ` K )
  assume cdlemg12.m: |- ./\ = ( meet ` K )
  assume cdlemg12.a: |- A = ( Atoms ` K )
  assume cdlemg12.h: |- H = ( LHyp ` K )
  assume cdlemg12.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg12b.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemg31.n: |- N = ( ( P .\/ v ) ./\ ( Q .\/ ( R ` F ) ) )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ Q e. A ) /\ ( v e. A /\ F e. T ) ) -> N .<_ ( P .\/ v ) )

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
    cQ
    cA
    wcel
    #
    wa
    #
    vv
    cv
    #
    cA
    wcel
    #
    cF
    cT
    wcel
    #
    wa
    #
    w3a
    #
    cN
    cP
    @6
    c.or
    co
    #
    cQ
    cF
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    #
    @11
    c.le
    cdlemg31.n
    @10
    cK
    clat
    wcel
    #
    @11
    cK
    cbs
    cfv
    #
    wcel
    #
    @13
    @16
    wcel
    #
    @14
    @11
    c.le
    wbr
    @10
    @0
    @15
    @0
    @1
    @5
    @9
    simp1l
    #
    cK
    hllat
    syl
    #
    @10
    @0
    @3
    @7
    @17
    @19
    @2
    @3
    @4
    @9
    simp2l
    @2
    @5
    @7
    @8
    simp3l
    cA
    @16
    c.or
    cK
    cP
    @6
    @16
    eqid
    #
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    @10
    @15
    cQ
    @16
    wcel
    #
    @12
    @16
    wcel
    #
    @18
    @20
    @10
    @4
    @22
    @2
    @3
    @4
    @9
    simp2r
    cA
    @16
    cQ
    cK
    @21
    cdlemg12.a
    atbase
    syl
    @10
    @2
    @8
    @23
    @2
    @5
    @9
    simp1
    @2
    @5
    @7
    @8
    simp3r
    @16
    cR
    cT
    cF
    cH
    cK
    cW
    @21
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    trlcl
    syl2anc
    @16
    c.or
    cK
    cQ
    @12
    @21
    cdlemg12.j
    latjcl
    syl3anc
    @16
    cK
    c.le
    c.an
    @11
    @13
    @21
    cdlemg12.l
    cdlemg12.m
    latmle1
    syl3anc
    syl5eqbr
end
