include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "simp32.mm"
include "simp31l.mm"
include "simp31r.mm"
include "simp1l.mm"
include "simp23.mm"
include "hlatlej2.mm"
include "syl3anc.mm"
include "simp33.mm"
include "breqtrd.mm"
include "cdleme22aa.mm"
include "syl133anc.mm"

theorem cdleme22a
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  assume cdleme22.l: |- .<_ = ( le ` K )
  assume cdleme22.j: |- .\/ = ( join ` K )
  assume cdleme22.m: |- ./\ = ( meet ` K )
  assume cdleme22.a: |- A = ( Atoms ` K )
  assume cdleme22.h: |- H = ( LHyp ` K )
  assume cdleme22.u: |- U = ( ( P .\/ Q ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ Q e. A /\ T e. A ) /\ ( ( V e. A /\ V .<_ W ) /\ P =/= Q /\ ( T .\/ V ) = ( P .\/ Q ) ) ) -> V = U )

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
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    cQ
    cA
    wcel
    #
    cT
    cA
    wcel
    #
    w3a
    #
    cV
    cA
    wcel
    #
    cV
    cW
    c.le
    wbr
    #
    wa
    #
    cP
    cQ
    wne
    #
    cT
    cV
    c.or
    co
    #
    cP
    cQ
    c.or
    co
    #
    wceq
    #
    w3a
    #
    w3a
    #
    @2
    @3
    @4
    @10
    @7
    @8
    cV
    @12
    c.le
    wbr
    cV
    cU
    wceq
    @2
    @6
    @14
    simp1
    @2
    @3
    @4
    @5
    @14
    simp21
    @2
    @3
    @4
    @5
    @14
    simp22
    @2
    @6
    @9
    @10
    @13
    simp32
    @7
    @8
    @10
    @13
    @2
    @6
    simp31l
    #
    @7
    @8
    @10
    @13
    @2
    @6
    simp31r
    @15
    cV
    @11
    @12
    c.le
    @15
    @0
    @5
    @7
    cV
    @11
    c.le
    wbr
    @0
    @1
    @6
    @14
    simp1l
    @2
    @3
    @4
    @5
    @14
    simp23
    @16
    cA
    cT
    cV
    c.or
    cK
    c.le
    cdleme22.l
    cdleme22.j
    cdleme22.a
    hlatlej2
    syl3anc
    @2
    @6
    @9
    @10
    @13
    simp33
    breqtrd
    cA
    cP
    cQ
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cdleme22.l
    cdleme22.j
    cdleme22.m
    cdleme22.a
    cdleme22.h
    cdleme22.u
    cdleme22aa
    syl133anc
end
