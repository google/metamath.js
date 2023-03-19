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
include "cdlemeg47rv.mm"
include "cv.mm"
include "wceq.mm"
include "simp22l.mm"
include "nfcvd.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "csbiegf.mm"
include "syl.mm"
include "simp23l.mm"
include "eqid.mm"
include "cdleme31se2.mm"
include "csbeq2dv.mm"
include "simp1.mm"
include "simp21.mm"
include "simp23.mm"
include "simp3r.mm"
include "cdlemeg47b.mm"
include "syl121anc.mm"
include "3eqtr4d.mm"
include "eqtrd.mm"

theorem cdlemeg47rv2
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
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
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R u
  disjoint R v
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) ) ) -> ( G ` R ) = ( ( Q .\/ P ) ./\ ( ( G ` S ) .\/ ( ( R .\/ S ) ./\ W ) ) ) )

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
    #
    cS
    @9
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cR
    cG
    cfv
    vu
    cR
    vv
    cS
    cO
    csb
    #
    csb
    #
    cQ
    cP
    c.or
    co
    #
    cS
    cG
    cfv
    #
    cR
    cS
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    #
    vv
    vu
    cA
    cB
    cP
    cQ
    cR
    cS
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cV
    cW
    va
    vb
    vc
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
    cdlemeg47rv
    @13
    vu
    cR
    @16
    vv
    cS
    cN
    csb
    #
    vu
    cv
    #
    cS
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    #
    csb
    #
    @16
    @22
    @19
    c.or
    co
    #
    c.an
    co
    #
    @15
    @21
    @13
    @2
    @28
    @30
    wceq
    @2
    @3
    @1
    @7
    @0
    @12
    simp22l
    vu
    cR
    @27
    @30
    cA
    @2
    vu
    @30
    nfcvd
    @23
    cR
    wceq
    #
    @26
    @29
    @16
    c.an
    @31
    @25
    @19
    @22
    c.or
    @31
    @24
    @18
    cW
    c.an
    @23
    cR
    cS
    c.or
    oveq1
    oveq1d
    oveq2d
    oveq2d
    csbiegf
    syl
    @13
    vu
    cR
    @14
    @27
    @13
    @5
    @14
    @27
    wceq
    @5
    @6
    @1
    @4
    @0
    @12
    simp23l
    vv
    cA
    cN
    cQ
    cP
    @23
    cS
    cO
    c.or
    c.an
    cW
    @27
    cdlemefs47.o
    @27
    eqid
    cdleme31se2
    syl
    csbeq2dv
    @13
    @20
    @29
    @16
    c.an
    @13
    @17
    @22
    @19
    c.or
    @13
    @0
    @1
    @7
    @11
    @17
    @22
    wceq
    @0
    @8
    @12
    simp1
    @0
    @1
    @4
    @7
    @12
    simp21
    @0
    @1
    @4
    @7
    @12
    simp23
    @0
    @8
    @10
    @11
    simp3r
    vv
    vu
    cA
    cB
    cP
    cQ
    cS
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cV
    cW
    va
    vb
    vc
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
    cdlemeg47b
    syl121anc
    oveq1d
    oveq2d
    3eqtr4d
    eqtrd
end
