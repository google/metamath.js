include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "simp11.mm"
include "simp13.mm"
include "simp12.mm"
include "simp2l.mm"
include "necomd.mm"
include "simp2r.mm"
include "simp3.mm"
include "cdleme48fv.mm"
include "syl321anc.mm"

theorem cdleme4gfv
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cR: class R
  assume cdlemef47.b: |- B = ( Base ` K )
  assume cdlemef47.l: |- .<_ = ( le ` K )
  assume cdlemef47.j: |- .\/ = ( join ` K )
  assume cdlemef47.m: |- ./\ = ( meet ` K )
  assume cdlemef47.a: |- A = ( Atoms ` K )
  assume cdlemef47.h: |- H = ( LHyp ` K )
  assume cdlemef47.v: |- V = ( ( Q .\/ P ) ./\ W )
  assume cdlemef47.n: |- N = ( ( v .\/ V ) ./\ ( P .\/ ( ( Q .\/ v ) ./\ W ) ) )
  assume cdlemefs47.o: |- O = ( ( Q .\/ P ) ./\ ( N .\/ ( ( u .\/ v ) ./\ W ) ) )
  assume cdlemef47.g: |- G = ( a e. B |-> if ( ( Q =/= P /\ -. a .<_ W ) , ( iota_ c e. B A. u e. A ( ( -. u .<_ W /\ ( u .\/ ( a ./\ W ) ) = a ) -> c = ( if ( u .<_ ( Q .\/ P ) , ( iota_ b e. B A. v e. A ( ( -. v .<_ W /\ -. v .<_ ( Q .\/ P ) ) -> b = O ) ) , [_ u / v ]_ N ) .\/ ( a ./\ W ) ) ) ) , a ) )

  disjoint a b
  disjoint a c
  disjoint a u
  disjoint a v
  disjoint A a
  disjoint b c
  disjoint b u
  disjoint b v
  disjoint A b
  disjoint c u
  disjoint c v
  disjoint A c
  disjoint u v
  disjoint A u
  disjoint A v
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B u
  disjoint B v
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H u
  disjoint H v
  disjoint .\/ a
  disjoint .\/ b
  disjoint .\/ c
  disjoint .\/ u
  disjoint .\/ v
  disjoint K a
  disjoint K b
  disjoint K c
  disjoint K u
  disjoint K v
  disjoint .<_ a
  disjoint .<_ b
  disjoint .<_ c
  disjoint .<_ u
  disjoint .<_ v
  disjoint ./\ a
  disjoint ./\ b
  disjoint ./\ c
  disjoint ./\ u
  disjoint ./\ v
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint N u
  disjoint O a
  disjoint O b
  disjoint O c
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P u
  disjoint P v
  disjoint Q a
  disjoint Q b
  disjoint Q c
  disjoint Q u
  disjoint Q v
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S u
  disjoint S v
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V u
  disjoint V v
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint W u
  disjoint W v
  disjoint X a
  disjoint X c
  disjoint X u
  disjoint X v
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R u
  disjoint R v
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( X e. B /\ -. X .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( S .\/ ( X ./\ W ) ) = X ) ) -> ( G ` X ) = ( ( G ` S ) .\/ ( X ./\ W ) ) )

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
    cX
    cB
    wcel
    cX
    cW
    c.le
    wbr
    wn
    wa
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
    cS
    cX
    cW
    c.an
    co
    #
    c.or
    co
    cX
    wceq
    wa
    #
    w3a
    #
    @0
    @2
    @1
    cQ
    cP
    wne
    @5
    @8
    cX
    cG
    cfv
    cS
    cG
    cfv
    @7
    c.or
    co
    wceq
    @0
    @1
    @2
    @6
    @8
    simp11
    @0
    @1
    @2
    @6
    @8
    simp13
    @0
    @1
    @2
    @6
    @8
    simp12
    @9
    cP
    cQ
    @3
    @4
    @5
    @8
    simp2l
    necomd
    @3
    @4
    @5
    @8
    simp2r
    @3
    @6
    @8
    simp3
    va
    vb
    vc
    vv
    cA
    cB
    cN
    cQ
    cP
    cS
    cV
    cO
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    vu
    cdlemef47.b
    cdlemef47.l
    cdlemef47.j
    cdlemef47.m
    cdlemef47.a
    cdlemef47.h
    cdlemef47.v
    cdlemef47.n
    cdlemefs47.o
    cdlemef47.g
    cdleme48fv
    syl321anc
end
