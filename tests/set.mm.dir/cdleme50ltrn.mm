include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cldil.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "eqid.mm"
include "cdleme50ldil.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp3l.mm"
include "cdleme50trn123.mm"
include "syl12anc.mm"
include "simp2r.mm"
include "simp3r.mm"
include "eqtr4d.mm"
include "3exp.mm"
include "ralrimivv.mm"
include "wb.mm"
include "isltrn.mm"
include "3ad2ant1.mm"
include "mpbir2and.mm"

theorem cdleme50ltrn
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vu: setvar u
  let vv: setvar v
  let cR: class R
  let cS: class S
  let cX: class X
  let cY: class Y
  let vd: setvar d
  let ve: setvar e
  let cG: class G
  let cN: class N
  let cO: class O
  let cV: class V
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
  assume cdleme50ltrn.t: |- T = ( ( LTrn ` K ) ` W )

  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint ./\ s
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint ./\ t
  disjoint x y
  disjoint x z
  disjoint ./\ x
  disjoint y z
  disjoint ./\ y
  disjoint ./\ z
  disjoint .\/ s
  disjoint .\/ t
  disjoint .\/ x
  disjoint .\/ y
  disjoint .\/ z
  disjoint .<_ s
  disjoint .<_ t
  disjoint .<_ x
  disjoint .<_ y
  disjoint .<_ z
  disjoint A s
  disjoint A t
  disjoint A x
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
  disjoint K s
  disjoint K t
  disjoint K x
  disjoint K y
  disjoint K z
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
  disjoint s u
  disjoint s v
  disjoint t u
  disjoint t v
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint ./\ u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint ./\ v
  disjoint .\/ a
  disjoint .\/ b
  disjoint .\/ c
  disjoint .\/ u
  disjoint .\/ v
  disjoint .<_ a
  disjoint .<_ b
  disjoint .<_ c
  disjoint .<_ u
  disjoint .<_ v
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A u
  disjoint A v
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B u
  disjoint B v
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D v
  disjoint E a
  disjoint E b
  disjoint E c
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F u
  disjoint F v
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H u
  disjoint H v
  disjoint K a
  disjoint K b
  disjoint K c
  disjoint K u
  disjoint K v
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
  disjoint U a
  disjoint U b
  disjoint U c
  disjoint U v
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint W u
  disjoint W v
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
  disjoint .\/ e
  disjoint ./\ e
  disjoint R e
  disjoint U e
  disjoint G d
  disjoint G e
  disjoint G s
  disjoint G t
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint N t
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
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V t
  disjoint V u
  disjoint V v
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint a e
  disjoint b e
  disjoint c e
  disjoint e u
  disjoint e v
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> F e. T )

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
    cF
    cT
    wcel
    #
    cF
    cW
    cK
    cldil
    cfv
    cfv
    #
    wcel
    #
    vd
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    ve
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    @7
    @7
    cF
    cfv
    c.or
    co
    cW
    c.an
    co
    #
    @9
    @9
    cF
    cfv
    c.or
    co
    cW
    c.an
    co
    #
    wceq
    #
    wi
    #
    ve
    cA
    wral
    vd
    cA
    wral
    #
    vx
    vy
    vz
    vt
    cA
    cB
    @5
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
    @5
    eqid
    #
    cdleme50ldil
    @3
    @15
    vd
    ve
    cA
    cA
    @3
    @7
    cA
    wcel
    #
    @9
    cA
    wcel
    #
    wa
    #
    @11
    @14
    @3
    @20
    @11
    w3a
    #
    @12
    cU
    @13
    @21
    @3
    @18
    @8
    @12
    cU
    wceq
    @3
    @20
    @11
    simp1
    #
    @3
    @18
    @19
    @11
    simp2l
    @3
    @20
    @8
    @10
    simp3l
    vx
    vy
    vz
    vt
    cA
    cB
    cD
    cP
    cQ
    @7
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
    cdleme50trn123
    syl12anc
    @21
    @3
    @19
    @10
    @13
    cU
    wceq
    @22
    @3
    @18
    @19
    @11
    simp2r
    @3
    @20
    @8
    @10
    simp3r
    vx
    vy
    vz
    vt
    cA
    cB
    cD
    cP
    cQ
    @9
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
    cdleme50trn123
    syl12anc
    eqtr4d
    3exp
    ralrimivv
    @0
    @1
    @4
    @6
    @16
    wa
    wb
    @2
    cA
    chlt
    @5
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    ve
    vd
    cdlemef50.l
    cdlemef50.j
    cdlemef50.m
    cdlemef50.a
    cdlemef50.h
    @17
    cdleme50ltrn.t
    isltrn
    3ad2ant1
    mpbir2and
end
