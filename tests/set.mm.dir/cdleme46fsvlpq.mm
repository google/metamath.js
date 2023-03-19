include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "csb.mm"
include "cif.mm"
include "eqid.mm"
include "cdlemefs32fva1.mm"
include "cvv.mm"
include "vex.mm"
include "cdleme31sc.mm"
include "ax-mp.mm"
include "cdleme41sn3a.mm"
include "eqbrtrd.mm"

theorem cdleme46fsvlpq
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ R .<_ ( P .\/ Q ) ) -> ( F ` R ) .<_ ( P .\/ Q ) )

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
    cP
    cQ
    wne
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    wa
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    w3a
    cR
    cF
    cfv
    vs
    cR
    vs
    cv
    #
    @0
    c.le
    wbr
    vt
    cv
    #
    cW
    c.le
    wbr
    wn
    @2
    @0
    c.le
    wbr
    wn
    wa
    #
    vy
    cv
    #
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
    vt
    @1
    cD
    csb
    #
    cif
    #
    csb
    @0
    c.le
    vx
    vy
    vz
    vt
    cA
    cB
    @6
    cD
    cP
    cQ
    cR
    cU
    cE
    cF
    cH
    @5
    c.or
    cK
    c.le
    c.an
    @7
    @1
    cW
    c.le
    wbr
    wn
    @1
    vx
    cv
    #
    cW
    c.an
    co
    #
    c.or
    co
    @8
    wceq
    wa
    vz
    cv
    @7
    @9
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
    cdlemef46.d
    cdlemefs46.e
    @5
    eqid
    #
    @7
    eqid
    #
    @10
    eqid
    cdlemef46.f
    cdlemefs32fva1
    vy
    vt
    cA
    cB
    @6
    cD
    cP
    cQ
    cR
    cU
    cE
    cH
    @5
    c.or
    cK
    c.le
    c.an
    @7
    cW
    @0
    cD
    cR
    @2
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
    @3
    @4
    @13
    wceq
    wi
    vt
    cA
    wral
    vy
    cB
    crio
    #
    vs
    cdlemef46.b
    cdlemef46.l
    cdlemef46.j
    cdlemef46.m
    cdlemef46.a
    cdlemef46.h
    cdlemef46.u
    @1
    cvv
    wcel
    @6
    @1
    cU
    c.or
    co
    cQ
    cP
    @1
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
    @1
    cU
    c.or
    c.an
    cW
    @15
    vt
    cdlemef46.d
    @15
    eqid
    cdleme31sc
    ax-mp
    cdlemef46.d
    cdlemefs46.e
    @11
    @12
    @13
    eqid
    @14
    eqid
    cdleme41sn3a
    eqbrtrd
end
