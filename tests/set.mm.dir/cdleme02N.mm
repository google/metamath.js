include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "cdleme01N.mm"
include "clc.mm"
include "wb.mm"
include "simp1l.mm"
include "hlcvl.mm"
include "syl.mm"
include "simp2ll.mm"
include "simp2rl.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp3.mm"
include "lhpat2.mm"
include "syl112anc.mm"
include "cvlsupr2.mm"
include "syl131anc.mm"
include "anbi1d.mm"
include "mpbird.mm"

theorem cdleme02N
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ P =/= Q ) -> ( ( P .\/ U ) = ( Q .\/ U ) /\ U .<_ W ) )

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
    cP
    cQ
    wne
    #
    w3a
    #
    cP
    cU
    c.or
    co
    cQ
    cU
    c.or
    co
    wceq
    #
    cU
    cW
    c.le
    wbr
    #
    wa
    cU
    cP
    wne
    cU
    cQ
    wne
    cU
    cP
    cQ
    c.or
    co
    c.le
    wbr
    w3a
    #
    @13
    wa
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
    cdleme01N
    @11
    @12
    @14
    @13
    @11
    cK
    clc
    wcel
    #
    @3
    @6
    cU
    cA
    wcel
    #
    @10
    @12
    @14
    wb
    @11
    @0
    @15
    @0
    @1
    @9
    @10
    simp1l
    cK
    hlcvl
    syl
    @3
    @4
    @8
    @2
    @10
    simp2ll
    @6
    @7
    @5
    @2
    @10
    simp2rl
    #
    @11
    @2
    @5
    @6
    @10
    @16
    @2
    @9
    @10
    simp1
    @2
    @5
    @8
    @10
    simp2l
    @17
    @2
    @9
    @10
    simp3
    #
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
    @18
    cA
    cP
    cQ
    cU
    c.or
    cK
    c.le
    cdleme0.a
    cdleme0.l
    cdleme0.j
    cvlsupr2
    syl131anc
    anbi1d
    mpbird
end
