include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "simp3r.mm"
include "wceq.mm"
include "simpl1l.mm"
include "simpl21.mm"
include "simpl1.mm"
include "simpl23.mm"
include "simpl22.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "simpl3l.mm"
include "ltrn11at.mm"
include "syl113anc.mm"
include "necomd.mm"
include "simpr.mm"
include "hlatexch4.mm"
include "syl323anc.mm"
include "eqcomd.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"

theorem cdlemg18a
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ Q e. A /\ F e. T ) /\ ( P =/= Q /\ ( ( F ` Q ) .\/ ( F ` P ) ) =/= ( P .\/ Q ) ) ) -> ( P .\/ ( F ` Q ) ) =/= ( Q .\/ ( F ` P ) ) )

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
    cF
    cT
    wcel
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cQ
    cF
    cfv
    #
    cP
    cF
    cfv
    #
    c.or
    co
    #
    cP
    cQ
    c.or
    co
    #
    wne
    #
    wa
    #
    w3a
    #
    @12
    cP
    @8
    c.or
    co
    #
    cQ
    @9
    c.or
    co
    #
    wne
    @2
    @6
    @7
    @12
    simp3r
    @14
    @15
    @16
    @10
    @11
    @14
    @15
    @16
    wceq
    #
    @10
    @11
    wceq
    @14
    @17
    wa
    #
    @11
    @10
    @18
    @0
    @3
    @8
    cA
    wcel
    #
    @4
    @9
    cA
    wcel
    #
    @7
    @8
    @9
    wne
    @17
    @11
    @10
    wceq
    @0
    @1
    @6
    @13
    @17
    simpl1l
    @3
    @4
    @5
    @2
    @13
    @17
    simpl21
    #
    @18
    @2
    @5
    @4
    @19
    @2
    @6
    @13
    @17
    simpl1
    #
    @3
    @4
    @5
    @2
    @13
    @17
    simpl23
    #
    @3
    @4
    @5
    @2
    @13
    @17
    simpl22
    #
    cA
    cQ
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg12.l
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    ltrnat
    syl3anc
    @24
    @18
    @2
    @5
    @3
    @20
    @22
    @23
    @21
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg12.l
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    ltrnat
    syl3anc
    @7
    @12
    @2
    @6
    @17
    simpl3l
    #
    @18
    @9
    @8
    @18
    @2
    @5
    @3
    @4
    @7
    @9
    @8
    wne
    @22
    @23
    @21
    @24
    @25
    cA
    cP
    cQ
    cT
    cF
    cH
    cK
    cW
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    ltrn11at
    syl113anc
    necomd
    @14
    @17
    simpr
    cA
    cP
    @8
    cQ
    @9
    c.or
    cK
    cdlemg12.j
    cdlemg12.a
    hlatexch4
    syl323anc
    eqcomd
    ex
    necon3d
    mpd
end
