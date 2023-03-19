include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "co.mm"
include "w3a.mm"
include "wceq.mm"
include "simp3rr.mm"
include "wb.mm"
include "simp1l.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "lhpat2.mm"
include "syl3anc.mm"
include "simp3rl.mm"
include "simp3ll.mm"
include "simp2ll.mm"
include "simp2rl.mm"
include "simp3l.mm"
include "cdleme0c.mm"
include "syl121anc.mm"
include "hlatexchb1.mm"
include "syl131anc.mm"
include "mpbid.mm"

theorem cdleme11a
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme11.l: |- .<_ = ( le ` K )
  assume cdleme11.j: |- .\/ = ( join ` K )
  assume cdleme11.m: |- ./\ = ( meet ` K )
  assume cdleme11.a: |- A = ( Atoms ` K )
  assume cdleme11.h: |- H = ( LHyp ` K )
  assume cdleme11.u: |- U = ( ( P .\/ Q ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ P =/= Q ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ U .<_ ( S .\/ T ) ) ) ) -> ( S .\/ U ) = ( S .\/ T ) )

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
    cP
    cQ
    wne
    #
    wa
    #
    wa
    #
    cS
    cA
    wcel
    #
    cS
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cT
    cA
    wcel
    #
    cU
    cS
    cT
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    wa
    #
    w3a
    #
    @15
    cS
    cU
    c.or
    co
    @14
    wceq
    #
    @13
    @15
    @12
    @2
    @9
    simp3rr
    @18
    @0
    cU
    cA
    wcel
    #
    @13
    @10
    cU
    cS
    wne
    #
    @15
    @19
    wb
    @0
    @1
    @9
    @17
    simp1l
    @18
    @2
    @5
    @8
    @20
    @2
    @9
    @17
    simp1
    #
    @2
    @5
    @8
    @17
    simp2l
    @2
    @5
    @8
    @17
    simp2r
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
    cdleme11.l
    cdleme11.j
    cdleme11.m
    cdleme11.a
    cdleme11.h
    cdleme11.u
    lhpat2
    syl3anc
    @13
    @15
    @12
    @2
    @9
    simp3rl
    @10
    @11
    @16
    @2
    @9
    simp3ll
    @18
    @2
    @3
    @6
    @12
    @21
    @22
    @3
    @4
    @8
    @2
    @17
    simp2ll
    @6
    @7
    @5
    @2
    @17
    simp2rl
    @2
    @9
    @12
    @16
    simp3l
    cA
    cP
    cQ
    cS
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme11.l
    cdleme11.j
    cdleme11.m
    cdleme11.a
    cdleme11.h
    cdleme11.u
    cdleme0c
    syl121anc
    cA
    cU
    cT
    cS
    c.or
    cK
    c.le
    cdleme11.l
    cdleme11.j
    cdleme11.a
    hlatexchb1
    syl131anc
    mpbid
end
