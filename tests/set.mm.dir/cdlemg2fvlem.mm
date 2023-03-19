include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cfv.mm"
include "simp1.mm"
include "simp3l.mm"
include "simp2r.mm"
include "simp2l.mm"
include "simp3r.mm"
include "jca.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "cv.mm"
include "cdleme48fvg.mm"
include "3expb.mm"
include "cdlemg2ce.mm"
include "syl112anc.mm"

theorem cdlemg2fvlem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vq: setvar q
  let vp: setvar p
  let vf: setvar f
  let cQ: class Q
  assume cdlemg2.b: |- B = ( Base ` K )
  assume cdlemg2.l: |- .<_ = ( le ` K )
  assume cdlemg2.j: |- .\/ = ( join ` K )
  assume cdlemg2.m: |- ./\ = ( meet ` K )
  assume cdlemg2.a: |- A = ( Atoms ` K )
  assume cdlemg2.h: |- H = ( LHyp ` K )
  assume cdlemg2.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg2ex.u: |- U = ( ( p .\/ q ) ./\ W )
  assume cdlemg2ex.d: |- D = ( ( t .\/ U ) ./\ ( q .\/ ( ( p .\/ t ) ./\ W ) ) )
  assume cdlemg2ex.e: |- E = ( ( p .\/ q ) ./\ ( D .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdlemg2ex.g: |- G = ( x e. B |-> if ( ( p =/= q /\ -. x .<_ W ) , ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( if ( s .<_ ( p .\/ q ) , ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( p .\/ q ) ) -> y = E ) ) , [_ s / t ]_ D ) .\/ ( x ./\ W ) ) ) ) , x ) )

  disjoint p q
  disjoint A p
  disjoint A q
  disjoint F p
  disjoint F q
  disjoint H p
  disjoint H q
  disjoint K p
  disjoint K q
  disjoint .<_ p
  disjoint .<_ q
  disjoint T p
  disjoint T q
  disjoint W p
  disjoint W q
  disjoint p s
  disjoint p t
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q s
  disjoint q t
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint .\/ p
  disjoint .\/ q
  disjoint P p
  disjoint P q
  disjoint B p
  disjoint B q
  disjoint ./\ p
  disjoint ./\ q
  disjoint X p
  disjoint X q
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
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint f p
  disjoint f q
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint Q p
  disjoint Q q
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint D f
  disjoint E f
  disjoint .\/ f
  disjoint ./\ f
  disjoint Q s
  disjoint Q t
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint F f
  disjoint A f
  disjoint H f
  disjoint K f
  disjoint .<_ f
  disjoint P f
  disjoint Q f
  disjoint T f
  disjoint W f
  disjoint G f
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( X e. B /\ -. X .<_ W ) ) /\ ( F e. T /\ ( P .\/ ( X ./\ W ) ) = X ) ) -> ( F ` X ) = ( ( F ` P ) .\/ ( X ./\ W ) ) )

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
    cF
    cT
    wcel
    #
    cP
    cX
    cW
    c.an
    co
    #
    c.or
    co
    cX
    wceq
    #
    wa
    #
    w3a
    #
    @0
    @4
    @2
    @1
    @6
    wa
    #
    cX
    cF
    cfv
    #
    cP
    cF
    cfv
    #
    @5
    c.or
    co
    #
    wceq
    #
    @0
    @3
    @7
    simp1
    @0
    @3
    @4
    @6
    simp3l
    @0
    @1
    @2
    @7
    simp2r
    @8
    @1
    @6
    @0
    @1
    @2
    @7
    simp2l
    @0
    @3
    @4
    @6
    simp3r
    jca
    @2
    @9
    wa
    @13
    cX
    cG
    cfv
    #
    cP
    cG
    cfv
    #
    @5
    c.or
    co
    #
    wceq
    #
    vx
    vy
    vz
    vt
    cA
    cB
    cD
    cT
    cU
    cE
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vs
    vq
    vp
    cdlemg2.b
    cdlemg2.l
    cdlemg2.j
    cdlemg2.m
    cdlemg2.a
    cdlemg2.h
    cdlemg2.t
    cdlemg2ex.u
    cdlemg2ex.d
    cdlemg2ex.e
    cdlemg2ex.g
    cF
    cG
    wceq
    #
    @10
    @14
    @12
    @16
    cX
    cF
    cG
    fveq1
    @18
    @11
    @15
    @5
    c.or
    cP
    cF
    cG
    fveq1
    oveq1d
    eqeq12d
    @0
    vp
    cv
    #
    cA
    wcel
    @19
    cW
    c.le
    wbr
    wn
    wa
    vq
    cv
    #
    cA
    wcel
    @20
    cW
    c.le
    wbr
    wn
    wa
    w3a
    @2
    @9
    @17
    vx
    vy
    vz
    vt
    cA
    cB
    cD
    @19
    @20
    cP
    cU
    cE
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    vs
    cdlemg2.b
    cdlemg2.l
    cdlemg2.j
    cdlemg2.m
    cdlemg2.a
    cdlemg2.h
    cdlemg2ex.u
    cdlemg2ex.d
    cdlemg2ex.e
    cdlemg2ex.g
    cdleme48fvg
    3expb
    cdlemg2ce
    syl112anc
end
