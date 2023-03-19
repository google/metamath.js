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
include "cdlemeg46c.mm"
include "syl.mm"
include "simp2rl.mm"
include "eqid.mm"
include "cdleme31snd.mm"
include "eqtrd.mm"
include "simp11l.mm"
include "simp12l.mm"
include "simp13l.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "3eqtr4g.mm"
include "oveq2d.mm"
include "cdleme35g.mm"
include "3eqtr2d.mm"

theorem cdlemeg46ngfr
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
  let cS: class S
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
  disjoint S s
  disjoint S t
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S u
  disjoint S v
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ -. R .<_ ( P .\/ Q ) ) -> ( G ` ( F ` R ) ) = R )

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
    #
    c.le
    wbr
    wn
    #
    w3a
    #
    cR
    cF
    cfv
    cG
    cfv
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
    cV
    c.or
    co
    #
    cP
    cQ
    @19
    c.or
    co
    cW
    c.an
    co
    c.or
    co
    #
    c.an
    co
    #
    @19
    cU
    c.or
    co
    #
    @21
    c.an
    co
    cR
    @17
    @18
    vt
    cR
    vv
    cD
    cN
    csb
    csb
    #
    @22
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
    cR
    cQ
    cP
    c.or
    co
    #
    c.le
    wbr
    wn
    w3a
    @18
    @24
    wceq
    cA
    cP
    cQ
    cR
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
    vt
    vs
    vv
    cA
    cB
    cN
    cQ
    cP
    cR
    cV
    cO
    cG
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cD
    cE
    cU
    cW
    vu
    vx
    vy
    vz
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
    cdlemef46g.u
    cdlemef46g.d
    cdlemefs46g.e
    cdlemef46g.f
    cdlemeg46c
    syl
    @17
    @11
    @24
    @22
    wceq
    @11
    @12
    @10
    @9
    @16
    simp2rl
    vt
    vv
    cA
    cN
    cQ
    cP
    cR
    cV
    @22
    c.or
    c.an
    cD
    @19
    cU
    cW
    cdlemef46.n
    cdlemef46g.d
    @22
    eqid
    @19
    eqid
    #
    cdleme31snd
    syl
    eqtrd
    @17
    @23
    @20
    @21
    c.an
    @17
    cU
    cV
    @19
    c.or
    @17
    @15
    cW
    c.an
    co
    @25
    cW
    c.an
    co
    cU
    cV
    @17
    @15
    @25
    cW
    c.an
    @17
    @0
    @3
    @6
    @15
    @25
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
    oveq1d
    cdlemef46g.u
    cdlemef46.v
    3eqtr4g
    oveq2d
    oveq1d
    cA
    cP
    cQ
    cR
    cU
    @19
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
    cdlemef46g.u
    @26
    cdleme35g
    3eqtr2d
end
