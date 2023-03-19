include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "wceq.mm"
include "simpll.mm"
include "simprl.mm"
include "simplr.mm"
include "simprr.mm"
include "jca.mm"
include "cdleme48gfv1.mm"
include "syl12anc.mm"
include "cv.mm"
include "co.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "csb.mm"
include "cif.mm"
include "cdleme31fv2.mm"
include "adantll.mm"
include "eqeltrd.mm"
include "simpr.mm"
include "wb.mm"
include "necom.mm"
include "a1i.mm"
include "breq1d.mm"
include "notbid.mm"
include "anbi12d.mm"
include "mtbird.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "pm2.61dan.mm"

theorem cdleme48gfv
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
  let cX: class X
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cR: class R
  let cS: class S
  let ve: setvar e
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
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint s u
  disjoint s v
  disjoint t u
  disjoint X a
  disjoint X c
  disjoint X s
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint X z
  disjoint R s
  disjoint R t
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S s
  disjoint S t
  disjoint S x
  disjoint S y
  disjoint S z
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
  disjoint A e
  disjoint F e
  disjoint G e
  disjoint H e
  disjoint .\/ e
  disjoint K e
  disjoint .<_ e
  disjoint P e
  disjoint Q e
  disjoint R e
  disjoint W e
  disjoint a e
  disjoint b e
  disjoint c e
  disjoint e s
  disjoint e t
  disjoint e u
  disjoint e v
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint B e
  disjoint ./\ e
  disjoint X e
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ X e. B ) -> ( G ` ( F ` X ) ) = X )

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
    cX
    cB
    wcel
    #
    wa
    #
    cP
    cQ
    wne
    #
    cX
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    cX
    cF
    cfv
    #
    cG
    cfv
    #
    cX
    wceq
    #
    @2
    @6
    wa
    #
    @0
    @3
    @1
    @5
    wa
    @9
    @0
    @1
    @6
    simpll
    @2
    @3
    @5
    simprl
    @10
    @1
    @5
    @0
    @1
    @6
    simplr
    @2
    @3
    @5
    simprr
    jca
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
    cX
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
    cdleme48gfv1
    syl12anc
    @2
    @6
    wn
    #
    wa
    #
    @8
    @7
    cX
    @12
    @7
    cB
    wcel
    cQ
    cP
    wne
    #
    @7
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    wn
    @8
    @7
    wceq
    @12
    @7
    cX
    cB
    @1
    @11
    @7
    cX
    wceq
    @0
    vx
    cB
    cP
    cQ
    cF
    c.le
    vs
    cv
    #
    cW
    c.le
    wbr
    wn
    @17
    vx
    cv
    #
    cW
    c.an
    co
    #
    c.or
    co
    @18
    wceq
    wa
    vz
    cv
    @17
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    vt
    cv
    #
    cW
    c.le
    wbr
    wn
    @21
    @20
    c.le
    wbr
    wn
    wa
    vy
    cv
    cE
    wceq
    wi
    vt
    cA
    wral
    vy
    cB
    crio
    vt
    @17
    cD
    csb
    cif
    @19
    c.or
    co
    wceq
    wi
    vs
    cA
    wral
    vz
    cB
    crio
    cW
    cX
    cdlemef46g.f
    cdleme31fv2
    adantll
    #
    @0
    @1
    @11
    simplr
    eqeltrd
    @12
    @16
    @6
    @2
    @11
    simpr
    @12
    @13
    @3
    @15
    @5
    @13
    @3
    wb
    @12
    cQ
    cP
    necom
    a1i
    @12
    @14
    @4
    @12
    @7
    cX
    cW
    c.le
    @22
    breq1d
    notbid
    anbi12d
    mtbird
    va
    cB
    cQ
    cP
    cG
    c.le
    vu
    cv
    #
    cW
    c.le
    wbr
    wn
    @23
    va
    cv
    #
    cW
    c.an
    co
    #
    c.or
    co
    @24
    wceq
    wa
    vc
    cv
    @23
    cQ
    cP
    c.or
    co
    #
    c.le
    wbr
    vv
    cv
    #
    cW
    c.le
    wbr
    wn
    @27
    @26
    c.le
    wbr
    wn
    wa
    vb
    cv
    cO
    wceq
    wi
    vv
    cA
    wral
    vb
    cB
    crio
    vv
    @23
    cN
    csb
    cif
    @25
    c.or
    co
    wceq
    wi
    vu
    cA
    wral
    vc
    cB
    crio
    cW
    @7
    cdlemef46.g
    cdleme31fv2
    syl2anc
    @22
    eqtrd
    pm2.61dan
end
