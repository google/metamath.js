include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "w3a.mm"
include "co.mm"
include "cv.mm"
include "wrex.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp3.mm"
include "lhpat2.mm"
include "syl112anc.mm"
include "simp2ll.mm"
include "cdlemeulpq.mm"
include "syl12anc.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi12d.mm"
include "rspcev.mm"

theorem cdleme0ex1N
  let vu: setvar u
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme0.l: |- .<_ = ( le ` K )
  assume cdleme0.j: |- .\/ = ( join ` K )
  assume cdleme0.m: |- ./\ = ( meet ` K )
  assume cdleme0.a: |- A = ( Atoms ` K )
  assume cdleme0.h: |- H = ( LHyp ` K )
  assume cdleme0.u: |- U = ( ( P .\/ Q ) ./\ W )

  disjoint A u
  disjoint .\/ u
  disjoint .<_ u
  disjoint P u
  disjoint Q u
  disjoint U u
  disjoint W u
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ Q e. A ) /\ P =/= Q ) -> E. u e. A ( u .<_ ( P .\/ Q ) /\ u .<_ W ) )

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
    wa
    #
    cP
    cQ
    wne
    #
    w3a
    #
    cU
    cA
    wcel
    #
    cU
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    cU
    cW
    c.le
    wbr
    #
    vu
    cv
    #
    @11
    c.le
    wbr
    #
    @14
    cW
    c.le
    wbr
    #
    wa
    #
    vu
    cA
    wrex
    @9
    @2
    @5
    @6
    @8
    @10
    @2
    @7
    @8
    simp1
    #
    @2
    @5
    @6
    @8
    simp2l
    @2
    @5
    @6
    @8
    simp2r
    #
    @2
    @7
    @8
    simp3
    cA
    cP
    cQ
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme0.l
    cdleme0.j
    cdleme0.m
    cdleme0.a
    cdleme0.h
    cdleme0.u
    lhpat2
    syl112anc
    @9
    @2
    @3
    @6
    @12
    @18
    @3
    @4
    @6
    @2
    @8
    simp2ll
    #
    @19
    cA
    cP
    cQ
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme0.l
    cdleme0.j
    cdleme0.m
    cdleme0.a
    cdleme0.h
    cdleme0.u
    cdlemeulpq
    syl12anc
    @9
    cU
    @11
    cW
    c.an
    co
    #
    cW
    c.le
    cdleme0.u
    @9
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
    cW
    @23
    wcel
    #
    @21
    cW
    c.le
    wbr
    @9
    @0
    @22
    @0
    @1
    @7
    @8
    simp1l
    #
    cK
    hllat
    syl
    @9
    @0
    @3
    @6
    @24
    @26
    @20
    @19
    cA
    @23
    c.or
    cK
    cP
    cQ
    @23
    eqid
    #
    cdleme0.j
    cdleme0.a
    hlatjcl
    syl3anc
    @9
    @1
    @25
    @0
    @1
    @7
    @8
    simp1r
    @23
    cH
    cK
    cW
    @27
    cdleme0.h
    lhpbase
    syl
    @23
    cK
    c.le
    c.an
    @11
    cW
    @27
    cdleme0.l
    cdleme0.m
    latmle2
    syl3anc
    syl5eqbr
    @17
    @12
    @13
    wa
    vu
    cU
    cA
    @14
    cU
    wceq
    @15
    @12
    @16
    @13
    @14
    cU
    @11
    c.le
    breq1
    @14
    cU
    cW
    c.le
    breq1
    anbi12d
    rspcev
    syl12anc
end
