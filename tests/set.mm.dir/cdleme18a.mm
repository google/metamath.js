include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23.mm"
include "simp3l.mm"
include "simp1l.mm"
include "simp21l.mm"
include "simp22l.mm"
include "hlatlej2.mm"
include "syl3anc.mm"
include "simp3r.mm"
include "cdleme7.mm"
include "syl323anc.mm"

theorem cdleme18a
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme18.l: |- .<_ = ( le ` K )
  assume cdleme18.j: |- .\/ = ( join ` K )
  assume cdleme18.m: |- ./\ = ( meet ` K )
  assume cdleme18.a: |- A = ( Atoms ` K )
  assume cdleme18.h: |- H = ( LHyp ` K )
  assume cdleme18.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme18.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme18.g: |- G = ( ( P .\/ Q ) ./\ ( F .\/ ( ( Q .\/ S ) ./\ W ) ) )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( P =/= Q /\ -. S .<_ ( P .\/ Q ) ) ) -> -. G .<_ W )

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
    cS
    cA
    wcel
    cS
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cS
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    @2
    @5
    @8
    @8
    @9
    @11
    cQ
    @12
    c.le
    wbr
    #
    @13
    cG
    cW
    c.le
    wbr
    wn
    @2
    @10
    @14
    simp1
    @2
    @5
    @8
    @9
    @14
    simp21
    @2
    @5
    @8
    @9
    @14
    simp22
    #
    @17
    @2
    @5
    @8
    @9
    @14
    simp23
    @2
    @10
    @11
    @13
    simp3l
    @15
    @0
    @3
    @6
    @16
    @0
    @1
    @10
    @14
    simp1l
    @3
    @4
    @8
    @9
    @2
    @14
    simp21l
    @6
    @7
    @5
    @9
    @2
    @14
    simp22l
    cA
    cP
    cQ
    c.or
    cK
    c.le
    cdleme18.l
    cdleme18.j
    cdleme18.a
    hlatlej2
    syl3anc
    @2
    @10
    @11
    @13
    simp3r
    cA
    cP
    cQ
    cQ
    cS
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme18.l
    cdleme18.j
    cdleme18.m
    cdleme18.a
    cdleme18.h
    cdleme18.u
    cdleme18.f
    cdleme18.g
    cdleme7
    syl323anc
end
