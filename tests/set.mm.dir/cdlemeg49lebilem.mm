include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "cv.mm"
include "csb.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "cif.mm"
include "cvv.mm"
include "vex.mm"
include "eqid.mm"
include "cdleme31sc.mm"
include "ax-mp.mm"
include "cdleme32le.mm"
include "3expia.mm"
include "simp1.mm"
include "simp2l.mm"
include "biid.mm"
include "ifbieq2i.mm"
include "cdleme32fvcl.mm"
include "syl2anc.mm"
include "simp2r.mm"
include "simp3.mm"
include "cdlemeg49le.mm"
include "syl121anc.mm"
include "wb.mm"
include "cdleme48gfv.mm"
include "adantrr.mm"
include "adantrl.mm"
include "breq12d.mm"
include "3adant3.mm"
include "mpbid.mm"
include "impbid.mm"

theorem cdlemeg49lebilem
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
  let cY: class Y
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
  disjoint Y a
  disjoint Y b
  disjoint Y c
  disjoint Y s
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y x
  disjoint Y y
  disjoint Y z
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( X e. B /\ Y e. B ) ) -> ( X .<_ Y <-> ( F ` X ) .<_ ( F ` Y ) ) )

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
    cY
    cB
    wcel
    #
    wa
    #
    wa
    #
    cX
    cY
    c.le
    wbr
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    c.le
    wbr
    #
    @0
    @3
    @5
    @8
    vx
    vy
    vz
    vt
    cA
    cB
    vt
    vs
    cv
    #
    cD
    csb
    #
    cD
    cP
    cQ
    cU
    cE
    cF
    cH
    vt
    cv
    #
    cW
    c.le
    wbr
    wn
    @11
    cP
    cQ
    c.or
    co
    #
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
    #
    c.or
    cK
    c.le
    c.an
    @9
    @12
    c.le
    wbr
    #
    @13
    @10
    cif
    #
    @9
    cW
    c.le
    wbr
    wn
    @9
    vx
    cv
    #
    cW
    c.an
    co
    #
    c.or
    co
    @16
    wceq
    wa
    vz
    cv
    @15
    @17
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
    #
    cW
    cX
    cY
    vs
    cdlemef46g.b
    cdlemef46g.l
    cdlemef46g.j
    cdlemef46g.m
    cdlemef46g.a
    cdlemef46g.h
    cdlemef46g.u
    @9
    cvv
    wcel
    @10
    @9
    cU
    c.or
    co
    cQ
    cP
    @9
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
    wceq
    vs
    vex
    cvv
    cD
    cP
    cQ
    @9
    cU
    c.or
    c.an
    cW
    @19
    vt
    cdlemef46g.d
    @19
    eqid
    #
    cdleme31sc
    ax-mp
    #
    cdlemef46g.d
    cdlemefs46g.e
    @13
    eqid
    #
    @15
    eqid
    @18
    eqid
    #
    cdlemef46g.f
    cdleme32le
    3expia
    @0
    @3
    @8
    @5
    @0
    @3
    @8
    w3a
    #
    @6
    cG
    cfv
    #
    @7
    cG
    cfv
    #
    c.le
    wbr
    #
    @5
    @24
    @0
    @6
    cB
    wcel
    #
    @7
    cB
    wcel
    #
    @8
    @27
    @0
    @3
    @8
    simp1
    #
    @24
    @0
    @1
    @28
    @30
    @0
    @1
    @2
    @8
    simp2l
    vx
    vy
    vz
    vt
    cA
    cB
    @19
    cD
    cP
    cQ
    cU
    cE
    cF
    cH
    @13
    c.or
    cK
    c.le
    c.an
    @15
    @18
    cW
    cX
    vs
    cdlemef46g.b
    cdlemef46g.l
    cdlemef46g.j
    cdlemef46g.m
    cdlemef46g.a
    cdlemef46g.h
    cdlemef46g.u
    @20
    cdlemef46g.d
    cdlemefs46g.e
    @22
    @14
    @14
    @10
    @19
    @13
    @14
    biid
    @21
    ifbieq2i
    #
    @23
    cdlemef46g.f
    cdleme32fvcl
    syl2anc
    @24
    @0
    @2
    @29
    @30
    @0
    @1
    @2
    @8
    simp2r
    vx
    vy
    vz
    vt
    cA
    cB
    @19
    cD
    cP
    cQ
    cU
    cE
    cF
    cH
    @13
    c.or
    cK
    c.le
    c.an
    @15
    @18
    cW
    cY
    vs
    cdlemef46g.b
    cdlemef46g.l
    cdlemef46g.j
    cdlemef46g.m
    cdlemef46g.a
    cdlemef46g.h
    cdlemef46g.u
    @20
    cdlemef46g.d
    cdlemefs46g.e
    @22
    @31
    @23
    cdlemef46g.f
    cdleme32fvcl
    syl2anc
    @0
    @3
    @8
    simp3
    vv
    vu
    cA
    cB
    cP
    cQ
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
    @6
    @7
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
    cdlemeg49le
    syl121anc
    @0
    @3
    @27
    @5
    wb
    @8
    @4
    @25
    cX
    @26
    cY
    c.le
    @0
    @1
    @25
    cX
    wceq
    @2
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
    cdleme48gfv
    adantrr
    @0
    @2
    @26
    cY
    wceq
    @1
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
    cY
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
    cdleme48gfv
    adantrl
    breq12d
    3adant3
    mpbid
    3expia
    impbid
end
