include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "simp11l.mm"
include "simp11r.mm"
include "simp12.mm"
include "simp13.mm"
include "simp31.mm"
include "simp2ll.mm"
include "simp2lr.mm"
include "simp12r.mm"
include "nbrne2.mm"
include "necomd.mm"
include "syl2anc.mm"
include "jca.mm"
include "simp33.mm"
include "4atex3.mm"
include "syl233anc.mm"
include "simp3.mm"
include "anim2i.mm"
include "reximi.mm"
include "syl.mm"

theorem cdlemg33c0
  let vz: setvar z
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

  disjoint A r
  disjoint .\/ r
  disjoint .<_ r
  disjoint P r
  disjoint Q r
  disjoint W r
  disjoint F r
  disjoint A z
  disjoint F z
  disjoint r z
  disjoint H r
  disjoint H z
  disjoint .\/ z
  disjoint K r
  disjoint K z
  disjoint .<_ z
  disjoint N r
  disjoint N z
  disjoint P z
  disjoint Q z
  disjoint R z
  disjoint T z
  disjoint W z
  disjoint v z
  disjoint r v
  disjoint G r
  disjoint S r
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( v e. A /\ v .<_ W ) /\ F e. T ) /\ ( P =/= Q /\ v =/= ( R ` F ) /\ E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> E. z e. A ( -. z .<_ W /\ z .<_ ( P .\/ v ) ) )

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
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    vv
    cv
    #
    cA
    wcel
    #
    @8
    cW
    c.le
    wbr
    #
    wa
    cF
    cT
    wcel
    #
    wa
    #
    cP
    cQ
    wne
    #
    @8
    cF
    cR
    cfv
    wne
    #
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @15
    c.or
    co
    cQ
    @15
    c.or
    co
    wceq
    wa
    vr
    cA
    wrex
    #
    w3a
    #
    w3a
    #
    vz
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @19
    cP
    wne
    #
    @19
    @8
    wne
    #
    @19
    cP
    @8
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    wa
    #
    vz
    cA
    wrex
    #
    @20
    @23
    wa
    #
    vz
    cA
    wrex
    @18
    @0
    @1
    @5
    @6
    @5
    @13
    @9
    cP
    @8
    wne
    #
    wa
    @16
    @26
    @0
    @1
    @5
    @6
    @12
    @17
    simp11l
    @0
    @1
    @5
    @6
    @12
    @17
    simp11r
    @2
    @5
    @6
    @12
    @17
    simp12
    #
    @2
    @5
    @6
    @12
    @17
    simp13
    @29
    @7
    @12
    @13
    @14
    @16
    simp31
    @18
    @9
    @28
    @9
    @10
    @11
    @7
    @17
    simp2ll
    @18
    @10
    @4
    @28
    @9
    @10
    @11
    @7
    @17
    simp2lr
    @3
    @4
    @2
    @6
    @12
    @17
    simp12r
    @10
    @4
    wa
    @8
    cP
    @8
    cP
    cW
    c.le
    nbrne2
    necomd
    syl2anc
    jca
    @7
    @12
    @13
    @14
    @16
    simp33
    vz
    cA
    cP
    cQ
    cP
    @8
    cH
    c.or
    cK
    c.le
    cW
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    cdlemg12.h
    4atex3
    syl233anc
    @25
    @27
    vz
    cA
    @24
    @23
    @20
    @21
    @22
    @23
    simp3
    anim2i
    reximi
    syl
end
