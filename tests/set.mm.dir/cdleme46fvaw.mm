include "cv.mm"
include "csb.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "cif.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "eqid.mm"
include "cdleme31sc.mm"
include "ax-mp.mm"
include "cdleme32fvaw.mm"

theorem cdleme46fvaw
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
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
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vs: setvar s
  let cS: class S
  let ve: setvar e
  let cX: class X
  assume cdlemef46.b: |- B = ( Base ` K )
  assume cdlemef46.l: |- .<_ = ( le ` K )
  assume cdlemef46.j: |- .\/ = ( join ` K )
  assume cdlemef46.m: |- ./\ = ( meet ` K )
  assume cdlemef46.a: |- A = ( Atoms ` K )
  assume cdlemef46.h: |- H = ( LHyp ` K )
  assume cdlemef46.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdlemef46.d: |- D = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdlemefs46.e: |- E = ( ( P .\/ Q ) ./\ ( D .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdlemef46.f: |- F = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( if ( s .<_ ( P .\/ Q ) , ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = E ) ) , [_ s / t ]_ D ) .\/ ( x ./\ W ) ) ) ) , x ) )

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
  disjoint A e
  disjoint F e
  disjoint H e
  disjoint .\/ e
  disjoint K e
  disjoint .<_ e
  disjoint P e
  disjoint Q e
  disjoint W e
  disjoint e s
  disjoint e t
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint X z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( R e. A /\ -. R .<_ W ) ) -> ( ( F ` R ) e. A /\ -. ( F ` R ) .<_ W ) )

  proof
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
    cR
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
    @2
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
    @0
    @3
    c.le
    wbr
    @4
    @1
    cif
    #
    @0
    cW
    c.le
    wbr
    wn
    @0
    vx
    cv
    #
    cW
    c.an
    co
    #
    c.or
    co
    @6
    wceq
    wa
    vz
    cv
    @5
    @7
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
    vs
    cdlemef46.b
    cdlemef46.l
    cdlemef46.j
    cdlemef46.m
    cdlemef46.a
    cdlemef46.h
    cdlemef46.u
    @0
    cvv
    wcel
    @1
    @0
    cU
    c.or
    co
    cQ
    cP
    @0
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
    @0
    cU
    c.or
    c.an
    cW
    @9
    vt
    cdlemef46.d
    @9
    eqid
    cdleme31sc
    ax-mp
    cdlemef46.d
    cdlemefs46.e
    @4
    eqid
    @5
    eqid
    @8
    eqid
    cdlemef46.f
    cdleme32fvaw
end
