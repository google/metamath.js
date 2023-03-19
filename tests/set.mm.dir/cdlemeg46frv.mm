include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cfv.mm"
include "cp0.mm"
include "wceq.mm"
include "simp11.mm"
include "simp1.mm"
include "simp22.mm"
include "cdleme46fvaw.mm"
include "syl2anc.mm"
include "eqid.mm"
include "lhpmat.mm"
include "oveq1d.mm"
include "simp11l.mm"
include "simpld.mm"
include "simp22l.mm"
include "simp23.mm"
include "simp21.mm"
include "cdlemeg46fvaw.mm"
include "syl3anc.mm"
include "cdleme0aa.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "syl.mm"
include "clat.mm"
include "hllat.mm"
include "hlatjcl.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "atmod4i2.mm"
include "syl131anc.mm"
include "col.mm"
include "hlol.mm"
include "olj02.mm"
include "3eqtr3d.mm"

theorem cdlemeg46frv
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
  let cR: class R
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
  let cY: class Y
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
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
  assume cdlemeg46.y: |- Y = ( ( R .\/ ( G ` S ) ) ./\ W )

  disjoint s t
  disjoint s x
  disjoint s z
  disjoint Y s
  disjoint t x
  disjoint t z
  disjoint Y t
  disjoint x z
  disjoint Y x
  disjoint Y z
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
  disjoint R s
  disjoint R t
  disjoint R x
  disjoint R y
  disjoint R z
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
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint E a
  disjoint E b
  disjoint E c
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F u
  disjoint F v
  disjoint N t
  disjoint U a
  disjoint U b
  disjoint U c
  disjoint U v
  disjoint V t
  disjoint a s
  disjoint a t
  disjoint b s
  disjoint b t
  disjoint c s
  disjoint c t
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) ) ) -> ( ( ( F ` R ) .\/ Y ) ./\ W ) = Y )

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
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    cS
    @12
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cR
    cF
    cfv
    #
    cW
    c.an
    co
    #
    cY
    c.or
    co
    #
    cK
    cp0
    cfv
    #
    cY
    c.or
    co
    #
    @15
    cY
    c.or
    co
    cW
    c.an
    co
    #
    cY
    @14
    @16
    @18
    cY
    c.or
    @14
    @2
    @15
    cA
    wcel
    #
    @15
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    @16
    @18
    wceq
    @2
    @3
    @4
    @11
    @13
    simp11
    #
    @14
    @5
    @9
    @23
    @5
    @11
    @13
    simp1
    #
    @5
    @6
    @9
    @10
    @13
    simp22
    vx
    vy
    vz
    vt
    cA
    cB
    cD
    cP
    cQ
    cR
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
    cdlemefs46g.e
    cdlemef46g.f
    cdleme46fvaw
    syl2anc
    #
    cA
    @15
    cH
    cK
    c.le
    c.an
    cW
    @18
    cdlemef46g.l
    cdlemef46g.m
    @18
    eqid
    #
    cdlemef46g.a
    cdlemef46g.h
    lhpmat
    syl2anc
    oveq1d
    @14
    @0
    @21
    cY
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    cY
    cW
    c.le
    wbr
    @17
    @20
    wceq
    @0
    @1
    @3
    @4
    @11
    @13
    simp11l
    #
    @14
    @21
    @22
    @26
    simpld
    @14
    @2
    @7
    cS
    cG
    cfv
    #
    cA
    wcel
    #
    @28
    @24
    @7
    @8
    @6
    @10
    @5
    @13
    simp22l
    #
    @14
    @5
    @10
    @6
    @32
    @25
    @5
    @6
    @9
    @10
    @13
    simp23
    @5
    @6
    @9
    @10
    @13
    simp21
    @5
    @10
    @6
    w3a
    @32
    @31
    cW
    c.le
    wbr
    wn
    vx
    vy
    vz
    vv
    vu
    vt
    cA
    cB
    cD
    cP
    cQ
    cS
    cU
    cE
    cF
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
    vs
    va
    vb
    vc
    cdlemef46g.b
    cdlemef46g.l
    cdlemef46g.j
    cdlemef46g.m
    cdlemef46g.a
    cdlemef46g.h
    cdlemef46g.u
    cdlemef46g.d
    cdlemefs46g.e
    cdlemef46g.f
    cdlemef46.v
    cdlemef46.n
    cdlemefs46.o
    cdlemef46.g
    cdlemeg46fvaw
    simpld
    syl3anc
    #
    cA
    cB
    cR
    @31
    cY
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemef46g.l
    cdlemef46g.j
    cdlemef46g.m
    cdlemef46g.a
    cdlemef46g.h
    cdlemeg46.y
    cdlemef46g.b
    cdleme0aa
    syl3anc
    #
    @14
    @1
    @29
    @0
    @1
    @3
    @4
    @11
    @13
    simp11r
    cB
    cH
    cK
    cW
    cdlemef46g.b
    cdlemef46g.h
    lhpbase
    syl
    #
    @14
    cY
    cR
    @31
    c.or
    co
    #
    cW
    c.an
    co
    #
    cW
    c.le
    cdlemeg46.y
    @14
    cK
    clat
    wcel
    #
    @37
    cB
    wcel
    #
    @29
    @38
    cW
    c.le
    wbr
    @14
    @0
    @39
    @30
    cK
    hllat
    syl
    @14
    @0
    @7
    @32
    @40
    @30
    @33
    @34
    cA
    cB
    c.or
    cK
    cR
    @31
    cdlemef46g.b
    cdlemef46g.j
    cdlemef46g.a
    hlatjcl
    syl3anc
    @36
    cB
    cK
    c.le
    c.an
    @37
    cW
    cdlemef46g.b
    cdlemef46g.l
    cdlemef46g.m
    latmle2
    syl3anc
    syl5eqbr
    cA
    cB
    @15
    c.or
    cK
    c.le
    c.an
    cY
    cW
    cdlemef46g.b
    cdlemef46g.l
    cdlemef46g.j
    cdlemef46g.m
    cdlemef46g.a
    atmod4i2
    syl131anc
    @14
    cK
    col
    wcel
    #
    @28
    @19
    cY
    wceq
    @14
    @0
    @41
    @30
    cK
    hlol
    syl
    @35
    cB
    c.or
    cK
    cY
    @18
    cdlemef46g.b
    cdlemef46g.j
    @27
    olj02
    syl2anc
    3eqtr3d
end
