include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cfv.mm"
include "csb.mm"
include "wceq.mm"
include "cdleme46f2g2.mm"
include "cdlemefr45.mm"
include "syl.mm"

theorem cdlemeg47b
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
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cR: class R
  let cX: class X
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
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R u
  disjoint R v
  disjoint X a
  disjoint X c
  disjoint X u
  disjoint X v
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( S e. A /\ -. S .<_ W ) ) /\ -. S .<_ ( P .\/ Q ) ) -> ( G ` S ) = [_ S / v ]_ N )

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
    cP
    cQ
    wne
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
    wa
    cS
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    w3a
    @0
    @2
    @1
    w3a
    cQ
    cP
    wne
    @3
    wa
    cS
    cQ
    cP
    c.or
    co
    c.le
    wbr
    wn
    w3a
    cS
    cG
    cfv
    vv
    cS
    cN
    csb
    wceq
    cA
    cP
    cQ
    cS
    cH
    c.or
    cK
    c.le
    cW
    cdlemef47.j
    cdlemef47.a
    cdleme46f2g2
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
    vu
    cdlemef47.b
    cdlemef47.l
    cdlemef47.j
    cdlemef47.m
    cdlemef47.a
    cdlemef47.h
    cdlemef47.v
    cdlemef47.n
    cdlemef47.g
    cdlemefr45
    syl
end
