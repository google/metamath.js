include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wne.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp31.mm"
include "simp2r.mm"
include "ltrnel.mm"
include "syl3anc.mm"
include "cdlemg42.mm"
include "cdlemc.mm"
include "syl131anc.mm"
include "trlval2.mm"
include "oveq2d.mm"
include "eqtr4d.mm"

theorem cdlemg43
  let cA: class A
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemg42.l: |- .<_ = ( le ` K )
  assume cdlemg42.j: |- .\/ = ( join ` K )
  assume cdlemg42.a: |- A = ( Atoms ` K )
  assume cdlemg42.h: |- H = ( LHyp ` K )
  assume cdlemg42.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg42.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemg42.m: |- ./\ = ( meet ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( G ` P ) =/= P /\ ( R ` F ) =/= ( R ` G ) ) ) -> ( F ` ( G ` P ) ) = ( ( ( G ` P ) .\/ ( R ` F ) ) ./\ ( ( F ` P ) .\/ ( R ` G ) ) ) )

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
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    cP
    cG
    cfv
    #
    cP
    wne
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
    w3a
    #
    w3a
    #
    @5
    cF
    cfv
    #
    @5
    @7
    c.or
    co
    #
    cP
    cF
    cfv
    #
    cP
    @5
    c.or
    co
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    #
    @13
    @14
    @8
    c.or
    co
    #
    c.an
    co
    @11
    @0
    @1
    @4
    @5
    cA
    wcel
    @5
    cW
    c.le
    wbr
    wn
    wa
    #
    @5
    cP
    @14
    c.or
    co
    c.le
    wbr
    wn
    @12
    @17
    wceq
    @0
    @3
    @10
    simp1
    #
    @0
    @1
    @2
    @10
    simp2l
    @0
    @3
    @4
    @6
    @9
    simp31
    #
    @11
    @0
    @2
    @4
    @19
    @20
    @0
    @1
    @2
    @10
    simp2r
    #
    @21
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg42.l
    cdlemg42.a
    cdlemg42.h
    cdlemg42.t
    ltrnel
    syl3anc
    cA
    cP
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    cW
    cdlemg42.l
    cdlemg42.j
    cdlemg42.a
    cdlemg42.h
    cdlemg42.t
    cdlemg42.r
    cdlemg42
    cA
    cP
    @5
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg42.l
    cdlemg42.j
    cdlemg42.m
    cdlemg42.a
    cdlemg42.h
    cdlemg42.t
    cdlemg42.r
    cdlemc
    syl131anc
    @11
    @18
    @16
    @13
    c.an
    @11
    @8
    @15
    @14
    c.or
    @11
    @0
    @2
    @4
    @8
    @15
    wceq
    @20
    @22
    @21
    cA
    cP
    cR
    cT
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg42.l
    cdlemg42.j
    cdlemg42.m
    cdlemg42.a
    cdlemg42.h
    cdlemg42.t
    cdlemg42.r
    trlval2
    syl3anc
    oveq2d
    oveq2d
    eqtr4d
end
