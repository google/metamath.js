include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "crn.mm"
include "wf.mm"
include "wss.mm"
include "cdleme50f.mm"
include "frn.mm"
include "syl.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "cdlemeg46fvcl.mm"
include "cdleme48fgv.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wfn.mm"
include "wb.mm"
include "adantr.mm"
include "ffn.mm"
include "fvelrnb.mm"
include "3syl.mm"
include "mpbird.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem cdleme50rnlem
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
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let cR: class R
  let cS: class S
  let cX: class X
  let cY: class Y
  assume cdlemef50.b: |- B = ( Base ` K )
  assume cdlemef50.l: |- .<_ = ( le ` K )
  assume cdlemef50.j: |- .\/ = ( join ` K )
  assume cdlemef50.m: |- ./\ = ( meet ` K )
  assume cdlemef50.a: |- A = ( Atoms ` K )
  assume cdlemef50.h: |- H = ( LHyp ` K )
  assume cdlemef50.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdlemef50.d: |- D = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdlemefs50.e: |- E = ( ( P .\/ Q ) ./\ ( D .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdlemef50.f: |- F = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( if ( s .<_ ( P .\/ Q ) , ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = E ) ) , [_ s / t ]_ D ) .\/ ( x ./\ W ) ) ) ) , x ) )
  assume cdlemef50.v: |- V = ( ( Q .\/ P ) ./\ W )
  assume cdlemef50.n: |- N = ( ( v .\/ V ) ./\ ( P .\/ ( ( Q .\/ v ) ./\ W ) ) )
  assume cdlemefs50.o: |- O = ( ( Q .\/ P ) ./\ ( N .\/ ( ( u .\/ v ) ./\ W ) ) )
  assume cdlemef50.g: |- G = ( a e. B |-> if ( ( Q =/= P /\ -. a .<_ W ) , ( iota_ c e. B A. u e. A ( ( -. u .<_ W /\ ( u .\/ ( a ./\ W ) ) = a ) -> c = ( if ( u .<_ ( Q .\/ P ) , ( iota_ b e. B A. v e. A ( ( -. v .<_ W /\ -. v .<_ ( Q .\/ P ) ) -> b = O ) ) , [_ u / v ]_ N ) .\/ ( a ./\ W ) ) ) ) , a ) )

  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint G s
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint G t
  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint a b
  disjoint a c
  disjoint a t
  disjoint a u
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint N a
  disjoint b c
  disjoint b t
  disjoint b u
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint N b
  disjoint c t
  disjoint c u
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint N c
  disjoint t u
  disjoint N t
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint N u
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint O a
  disjoint O b
  disjoint O c
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint a v
  disjoint V a
  disjoint b v
  disjoint V b
  disjoint c v
  disjoint V c
  disjoint t v
  disjoint V t
  disjoint u v
  disjoint V u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint V v
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint a b
  disjoint a c
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint ./\ a
  disjoint b c
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint ./\ b
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint ./\ c
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint ./\ s
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint ./\ t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint ./\ u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint ./\ v
  disjoint x y
  disjoint x z
  disjoint ./\ x
  disjoint y z
  disjoint ./\ y
  disjoint ./\ z
  disjoint .\/ a
  disjoint .\/ b
  disjoint .\/ c
  disjoint .\/ s
  disjoint .\/ t
  disjoint .\/ u
  disjoint .\/ v
  disjoint .\/ x
  disjoint .\/ y
  disjoint .\/ z
  disjoint .<_ a
  disjoint .<_ b
  disjoint .<_ c
  disjoint .<_ s
  disjoint .<_ t
  disjoint .<_ u
  disjoint .<_ v
  disjoint .<_ x
  disjoint .<_ y
  disjoint .<_ z
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A s
  disjoint A t
  disjoint A u
  disjoint A v
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B s
  disjoint B t
  disjoint B u
  disjoint B v
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D s
  disjoint D v
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint E a
  disjoint E b
  disjoint E c
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F u
  disjoint F v
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H s
  disjoint H t
  disjoint H u
  disjoint H v
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint K a
  disjoint K b
  disjoint K c
  disjoint K s
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P s
  disjoint P t
  disjoint P u
  disjoint P v
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint Q a
  disjoint Q b
  disjoint Q c
  disjoint Q s
  disjoint Q t
  disjoint Q u
  disjoint Q v
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint U a
  disjoint U b
  disjoint U c
  disjoint U s
  disjoint U t
  disjoint U v
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint W s
  disjoint W t
  disjoint W u
  disjoint W v
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint d s
  disjoint d t
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint G d
  disjoint a e
  disjoint c e
  disjoint e u
  disjoint e v
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
  disjoint X a
  disjoint X c
  disjoint X s
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint X y
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
  disjoint d e
  disjoint A d
  disjoint A e
  disjoint B d
  disjoint B e
  disjoint F d
  disjoint F e
  disjoint H d
  disjoint H e
  disjoint K d
  disjoint K e
  disjoint .<_ d
  disjoint .<_ e
  disjoint P d
  disjoint P e
  disjoint Q d
  disjoint Q e
  disjoint W d
  disjoint W e
  disjoint d s
  disjoint d t
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint e s
  disjoint e t
  disjoint e x
  disjoint e y
  disjoint e z
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> ran F = B )

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
    cF
    crn
    #
    cB
    @0
    cB
    cB
    cF
    wf
    #
    @1
    cB
    wss
    vx
    vy
    vz
    vt
    cA
    cB
    cD
    cP
    cQ
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
    cdlemef50.b
    cdlemef50.l
    cdlemef50.j
    cdlemef50.m
    cdlemef50.a
    cdlemef50.h
    cdlemef50.u
    cdlemef50.d
    cdlemefs50.e
    cdlemef50.f
    cdleme50f
    #
    cB
    cB
    cF
    frn
    syl
    @0
    ve
    cB
    @1
    @0
    ve
    cv
    #
    cB
    wcel
    #
    @4
    @1
    wcel
    #
    @0
    @5
    wa
    #
    @6
    vd
    cv
    #
    cF
    cfv
    #
    @4
    wceq
    #
    vd
    cB
    wrex
    #
    @7
    @4
    cG
    cfv
    #
    cB
    wcel
    @12
    cF
    cfv
    #
    @4
    wceq
    #
    @11
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
    @4
    va
    vb
    vc
    cdlemef50.b
    cdlemef50.l
    cdlemef50.j
    cdlemef50.m
    cdlemef50.a
    cdlemef50.h
    cdlemef50.v
    cdlemef50.n
    cdlemefs50.o
    cdlemef50.g
    cdlemeg46fvcl
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
    @4
    vs
    va
    vb
    vc
    cdlemef50.b
    cdlemef50.l
    cdlemef50.j
    cdlemef50.m
    cdlemef50.a
    cdlemef50.h
    cdlemef50.u
    cdlemef50.d
    cdlemefs50.e
    cdlemef50.f
    cdlemef50.v
    cdlemef50.n
    cdlemefs50.o
    cdlemef50.g
    cdleme48fgv
    @10
    @14
    vd
    @12
    cB
    @8
    @12
    wceq
    @9
    @13
    @4
    @8
    @12
    cF
    fveq2
    eqeq1d
    rspcev
    syl2anc
    @7
    @2
    cF
    cB
    wfn
    @6
    @11
    wb
    @0
    @2
    @5
    @3
    adantr
    cB
    cB
    cF
    ffn
    vd
    cB
    @4
    cF
    fvelrnb
    3syl
    mpbird
    ex
    ssrdv
    eqssd
end
