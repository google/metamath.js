include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "csb.mm"
include "eqid.mm"
include "cdleme35h2.mm"
include "wceq.mm"
include "simp22l.mm"
include "simp31.mm"
include "cdleme31sn2.mm"
include "syl2anc.mm"
include "simp23l.mm"
include "simp32.mm"
include "3netr4d.mm"

theorem cdleme35sn2aw
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
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
  assume cdleme32s.b: |- B = ( Base ` K )
  assume cdleme32s.l: |- .<_ = ( le ` K )
  assume cdleme32s.j: |- .\/ = ( join ` K )
  assume cdleme32s.m: |- ./\ = ( meet ` K )
  assume cdleme32s.a: |- A = ( Atoms ` K )
  assume cdleme32s.h: |- H = ( LHyp ` K )
  assume cdleme32s.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme32s.d: |- D = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdleme32s.n: |- N = if ( s .<_ ( P .\/ Q ) , I , D )

  disjoint A s
  disjoint B s
  disjoint H s
  disjoint .\/ s
  disjoint K s
  disjoint .<_ s
  disjoint ./\ s
  disjoint P s
  disjoint Q s
  disjoint R s
  disjoint S s
  disjoint U s
  disjoint W s
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( -. R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) /\ R =/= S ) ) -> [_ R / s ]_ N =/= [_ S / s ]_ N )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
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
    w3a
    #
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cS
    @9
    c.le
    wbr
    wn
    #
    cR
    cS
    wne
    #
    w3a
    #
    w3a
    #
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
    cS
    cU
    c.or
    co
    cQ
    cP
    cS
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
    vs
    cR
    cN
    csb
    #
    vs
    cS
    cN
    csb
    #
    cA
    cP
    cQ
    cR
    cS
    cU
    @15
    @16
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme32s.l
    cdleme32s.j
    cdleme32s.m
    cdleme32s.a
    cdleme32s.h
    cdleme32s.u
    @15
    eqid
    #
    @16
    eqid
    #
    cdleme35h2
    @14
    @2
    @10
    @17
    @15
    wceq
    @2
    @3
    @1
    @7
    @0
    @13
    simp22l
    @0
    @8
    @10
    @11
    @12
    simp31
    cA
    @15
    cD
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
    cdleme32s.d
    cdleme32s.n
    @19
    cdleme31sn2
    syl2anc
    @14
    @5
    @11
    @18
    @16
    wceq
    @5
    @6
    @1
    @4
    @0
    @13
    simp23l
    @0
    @8
    @10
    @11
    @12
    simp32
    cA
    @16
    cD
    cP
    cQ
    cS
    cU
    cI
    c.or
    c.le
    c.an
    cN
    cW
    vs
    cdleme32s.d
    cdleme32s.n
    @20
    cdleme31sn2
    syl2anc
    3netr4d
end
