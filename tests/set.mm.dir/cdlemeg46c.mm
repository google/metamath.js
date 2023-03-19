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
include "cdlemeg47b.mm"
include "csbeq1d.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp11.mm"
include "simp13.mm"
include "simp12.mm"
include "simp2r.mm"
include "cdleme46fvaw.mm"
include "syl31anc.mm"
include "cdleme46f2g2.mm"
include "cdleme46frvlpq.mm"
include "syl.mm"
include "simp11l.mm"
include "simp12l.mm"
include "simp13l.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "breq2d.mm"
include "mtbird.mm"
include "cdlemefr45.mm"
include "syl121anc.mm"
include "simp2rl.mm"
include "csbnestg.mm"
include "3eqtr4d.mm"

theorem cdlemeg46c
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
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
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cR: class R
  assume cdlemef46g.b: |- B = ( Base ` K )
  assume cdlemef46g.l: |- .<_ = ( le ` K )
  assume cdlemef46g.j: |- .\/ = ( join ` K )
  assume cdlemef46g.m: |- ./\ = ( meet ` K )
  assume cdlemef46g.a: |- A = ( Atoms ` K )
  assume cdlemef46g.h: |- H = ( LHyp ` K )
  assume cdlemef46g.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdlemef46g.d: |- D = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdlemefs46g.e: |- E = ( ( P .\/ Q ) ./\ ( D .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdlemef46g.f: |- F = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( if ( s .<_ ( P .\/ Q ) , ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = E ) ) , [_ s / t ]_ D ) .\/ ( x ./\ W ) ) ) ) , x ) )
  assume cdlemef46.v: |- V = ( ( Q .\/ P ) ./\ W )
  assume cdlemef46.n: |- N = ( ( v .\/ V ) ./\ ( P .\/ ( ( Q .\/ v ) ./\ W ) ) )
  assume cdlemefs46.o: |- O = ( ( Q .\/ P ) ./\ ( N .\/ ( ( u .\/ v ) ./\ W ) ) )
  assume cdlemef46.g: |- G = ( a e. B |-> if ( ( Q =/= P /\ -. a .<_ W ) , ( iota_ c e. B A. u e. A ( ( -. u .<_ W /\ ( u .\/ ( a ./\ W ) ) = a ) -> c = ( if ( u .<_ ( Q .\/ P ) , ( iota_ b e. B A. v e. A ( ( -. v .<_ W /\ -. v .<_ ( Q .\/ P ) ) -> b = O ) ) , [_ u / v ]_ N ) .\/ ( a ./\ W ) ) ) ) , a ) )

  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B s
  disjoint B t
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint D s
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint H s
  disjoint H t
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint .\/ s
  disjoint .\/ t
  disjoint .\/ x
  disjoint .\/ y
  disjoint .\/ z
  disjoint K s
  disjoint K t
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint .<_ s
  disjoint .<_ t
  disjoint .<_ x
  disjoint .<_ y
  disjoint .<_ z
  disjoint ./\ s
  disjoint ./\ t
  disjoint ./\ x
  disjoint ./\ y
  disjoint ./\ z
  disjoint P s
  disjoint P t
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint Q s
  disjoint Q t
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint U s
  disjoint U t
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint W s
  disjoint W t
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint S s
  disjoint S t
  disjoint S x
  disjoint S y
  disjoint S z
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
  disjoint D v
  disjoint G s
  disjoint G t
  disjoint G x
  disjoint G y
  disjoint G z
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
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint W u
  disjoint W v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint N u
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint t v
  disjoint V u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint V v
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint R s
  disjoint R t
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R u
  disjoint R v
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( S e. A /\ -. S .<_ W ) ) /\ -. S .<_ ( P .\/ Q ) ) -> ( F ` ( G ` S ) ) = [_ S / v ]_ [_ N / t ]_ D )

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
    w3a
    #
    cP
    cQ
    wne
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
    wa
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
    w3a
    #
    vt
    cS
    cG
    cfv
    #
    cD
    csb
    #
    vt
    vv
    cS
    cN
    csb
    #
    cD
    csb
    #
    @18
    cF
    cfv
    #
    vv
    cS
    vt
    cN
    cD
    csb
    csb
    #
    @17
    vt
    @18
    @20
    cD
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
    cdlemef46g.b
    cdlemef46g.l
    cdlemef46g.j
    cdlemef46g.m
    cdlemef46g.a
    cdlemef46g.h
    cdlemef46.v
    cdlemef46.n
    cdlemefs46.o
    cdlemef46.g
    cdlemeg47b
    csbeq1d
    @17
    @9
    @10
    @18
    cA
    wcel
    @18
    cW
    c.le
    wbr
    wn
    wa
    #
    @18
    @15
    c.le
    wbr
    #
    wn
    @22
    @19
    wceq
    @9
    @14
    @16
    simp1
    @9
    @10
    @13
    @16
    simp2l
    @17
    @2
    @8
    @5
    @13
    @24
    @2
    @5
    @8
    @14
    @16
    simp11
    @2
    @5
    @8
    @14
    @16
    simp13
    @2
    @5
    @8
    @14
    @16
    simp12
    @9
    @10
    @13
    @16
    simp2r
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
    cdlemef46g.b
    cdlemef46g.l
    cdlemef46g.j
    cdlemef46g.m
    cdlemef46g.a
    cdlemef46g.h
    cdlemef46.v
    cdlemef46.n
    cdlemefs46.o
    cdlemef46.g
    cdleme46fvaw
    syl31anc
    @17
    @25
    @18
    cQ
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    @17
    @2
    @8
    @5
    w3a
    cQ
    cP
    wne
    @13
    wa
    cS
    @26
    c.le
    wbr
    wn
    w3a
    @27
    wn
    cA
    cP
    cQ
    cS
    cH
    c.or
    cK
    c.le
    cW
    cdlemef46g.j
    cdlemef46g.a
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
    cdlemef46g.b
    cdlemef46g.l
    cdlemef46g.j
    cdlemef46g.m
    cdlemef46g.a
    cdlemef46g.h
    cdlemef46.v
    cdlemef46.n
    cdlemefs46.o
    cdlemef46.g
    cdleme46frvlpq
    syl
    @17
    @15
    @26
    @18
    c.le
    @17
    @0
    @3
    @6
    @15
    @26
    wceq
    @0
    @1
    @5
    @8
    @14
    @16
    simp11l
    @3
    @4
    @2
    @8
    @14
    @16
    simp12l
    @6
    @7
    @2
    @5
    @14
    @16
    simp13l
    cA
    c.or
    cK
    cP
    cQ
    cdlemef46g.j
    cdlemef46g.a
    hlatjcom
    syl3anc
    breq2d
    mtbird
    vx
    vy
    vz
    vt
    cA
    cB
    cD
    cP
    cQ
    @18
    cU
    cE
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vs
    cdlemef46g.b
    cdlemef46g.l
    cdlemef46g.j
    cdlemef46g.m
    cdlemef46g.a
    cdlemef46g.h
    cdlemef46g.u
    cdlemef46g.d
    cdlemef46g.f
    cdlemefr45
    syl121anc
    @17
    @11
    @23
    @21
    wceq
    @11
    @12
    @10
    @9
    @16
    simp2rl
    vv
    vt
    cS
    cN
    cD
    cA
    csbnestg
    syl
    3eqtr4d
end
