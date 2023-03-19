include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "csb.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp2r.mm"
include "simp2l.mm"
include "simp3.mm"
include "eqid.mm"
include "cdleme3fa.mm"
include "cdleme3.mm"
include "jca.mm"
include "syl132anc.mm"
include "wceq.mm"
include "simp2rl.mm"
include "cdleme31sn2.mm"
include "syl2anc.mm"
include "eleq1d.mm"
include "breq1d.mm"
include "notbid.mm"
include "anbi12d.mm"
include "mpbird.mm"

theorem cdlemefr32sn2aw
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let vs: setvar s
  assume cdlemefr27.b: |- B = ( Base ` K )
  assume cdlemefr27.l: |- .<_ = ( le ` K )
  assume cdlemefr27.j: |- .\/ = ( join ` K )
  assume cdlemefr27.m: |- ./\ = ( meet ` K )
  assume cdlemefr27.a: |- A = ( Atoms ` K )
  assume cdlemefr27.h: |- H = ( LHyp ` K )
  assume cdlemefr27.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdlemefr27.c: |- C = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdlemefr27.n: |- N = if ( s .<_ ( P .\/ Q ) , I , C )

  disjoint A s
  disjoint .\/ s
  disjoint .<_ s
  disjoint ./\ s
  disjoint P s
  disjoint Q s
  disjoint R s
  disjoint U s
  disjoint W s
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ -. R .<_ ( P .\/ Q ) ) -> ( [_ R / s ]_ N e. A /\ -. [_ R / s ]_ N .<_ W ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    cQ
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
    cR
    cA
    wcel
    #
    cR
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    cR
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    #
    w3a
    #
    vs
    cR
    cN
    csb
    #
    cA
    wcel
    #
    @11
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    cR
    cU
    c.or
    co
    cQ
    cP
    cR
    c.or
    co
    cW
    c.an
    co
    c.or
    co
    c.an
    co
    #
    cA
    wcel
    #
    @15
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    @10
    @0
    @1
    @2
    @7
    @4
    @9
    @19
    @0
    @1
    @2
    @8
    @9
    simp11
    @0
    @1
    @2
    @8
    @9
    simp12
    @0
    @1
    @2
    @8
    @9
    simp13
    @3
    @4
    @7
    @9
    simp2r
    @3
    @4
    @7
    @9
    simp2l
    @3
    @8
    @9
    simp3
    #
    @0
    @1
    @2
    @7
    w3a
    @4
    @9
    wa
    w3a
    @16
    @18
    cA
    cP
    cQ
    cR
    cU
    @15
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemefr27.l
    cdlemefr27.j
    cdlemefr27.m
    cdlemefr27.a
    cdlemefr27.h
    cdlemefr27.u
    @15
    eqid
    #
    cdleme3fa
    cA
    cP
    cQ
    cR
    cU
    @15
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemefr27.l
    cdlemefr27.j
    cdlemefr27.m
    cdlemefr27.a
    cdlemefr27.h
    cdlemefr27.u
    @21
    cdleme3
    jca
    syl132anc
    @10
    @12
    @16
    @14
    @18
    @10
    @11
    @15
    cA
    @10
    @5
    @9
    @11
    @15
    wceq
    @5
    @6
    @4
    @3
    @9
    simp2rl
    @20
    cA
    @15
    cC
    cP
    cQ
    cR
    cU
    cI
    c.or
    c.le
    c.an
    cN
    cW
    vs
    cdlemefr27.c
    cdlemefr27.n
    @21
    cdleme31sn2
    syl2anc
    #
    eleq1d
    @10
    @13
    @17
    @10
    @11
    @15
    cW
    c.le
    @22
    breq1d
    notbid
    anbi12d
    mpbird
end
