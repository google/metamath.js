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
include "cdleme35fnpq.mm"
include "wceq.mm"
include "simp2rl.mm"
include "simp3.mm"
include "cdleme31sn2.mm"
include "syl2anc.mm"
include "breq1d.mm"
include "mtbird.mm"

theorem cdleme35sn3a
  let cA: class A
  let cB: class B
  let cD: class D
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
  let cS: class S
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
  disjoint U s
  disjoint W s
  disjoint S s
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ -. R .<_ ( P .\/ Q ) ) -> -. [_ R / s ]_ N .<_ ( P .\/ Q ) )

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
    wa
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
    w3a
    #
    vs
    cR
    cN
    csb
    #
    @5
    c.le
    wbr
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
    @5
    c.le
    wbr
    cA
    cP
    cQ
    cR
    cU
    @9
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
    @9
    eqid
    #
    cdleme35fnpq
    @7
    @8
    @9
    @5
    c.le
    @7
    @2
    @6
    @8
    @9
    wceq
    @2
    @3
    @1
    @0
    @6
    simp2rl
    @0
    @4
    @6
    simp3
    cA
    @9
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
    @10
    cdleme31sn2
    syl2anc
    breq1d
    mtbird
end
