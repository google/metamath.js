include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr2.mm"
include "simpr3.mm"
include "simpr1.mm"
include "eqid.mm"
include "cdleme42g.mm"
include "syl121anc.mm"
include "cdleme42ke.mm"
include "eqtr4d.mm"

theorem cdleme42mN
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
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let vs: setvar s
  let vu: setvar u
  let cX: class X
  assume cdleme41.b: |- B = ( Base ` K )
  assume cdleme41.l: |- .<_ = ( le ` K )
  assume cdleme41.j: |- .\/ = ( join ` K )
  assume cdleme41.m: |- ./\ = ( meet ` K )
  assume cdleme41.a: |- A = ( Atoms ` K )
  assume cdleme41.h: |- H = ( LHyp ` K )
  assume cdleme41.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme41.d: |- D = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdleme41.e: |- E = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdleme41.g: |- G = ( ( P .\/ Q ) ./\ ( E .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdleme41.i: |- I = ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = G ) )
  assume cdleme41.n: |- N = if ( s .<_ ( P .\/ Q ) , I , D )
  assume cdleme41.o: |- O = ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( N .\/ ( x ./\ W ) ) ) )
  assume cdleme41.f: |- F = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , O , x ) )

  disjoint A s
  disjoint .\/ s
  disjoint .<_ s
  disjoint ./\ s
  disjoint P s
  disjoint Q s
  disjoint R s
  disjoint S s
  disjoint U s
  disjoint W s
  disjoint t y
  disjoint A t
  disjoint A y
  disjoint s t
  disjoint s y
  disjoint B s
  disjoint B t
  disjoint B y
  disjoint D y
  disjoint G y
  disjoint E s
  disjoint E y
  disjoint H s
  disjoint H t
  disjoint H y
  disjoint .\/ t
  disjoint .\/ y
  disjoint K s
  disjoint K t
  disjoint K y
  disjoint .<_ t
  disjoint .<_ y
  disjoint ./\ t
  disjoint ./\ y
  disjoint P t
  disjoint P y
  disjoint Q t
  disjoint Q y
  disjoint R t
  disjoint R y
  disjoint S t
  disjoint S y
  disjoint U t
  disjoint U y
  disjoint W t
  disjoint W y
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint B x
  disjoint B z
  disjoint E z
  disjoint s z
  disjoint H z
  disjoint .\/ x
  disjoint .\/ z
  disjoint K z
  disjoint .<_ x
  disjoint .<_ z
  disjoint ./\ x
  disjoint ./\ z
  disjoint N x
  disjoint N z
  disjoint P x
  disjoint P z
  disjoint Q x
  disjoint Q z
  disjoint R x
  disjoint R z
  disjoint S x
  disjoint S z
  disjoint U x
  disjoint U z
  disjoint W x
  disjoint W z
  disjoint s x
  disjoint t x
  disjoint t z
  disjoint x y
  disjoint y z
  disjoint s u
  disjoint A u
  disjoint .\/ u
  disjoint .<_ u
  disjoint ./\ u
  disjoint N u
  disjoint P u
  disjoint Q u
  disjoint S u
  disjoint U u
  disjoint t u
  disjoint u y
  disjoint B u
  disjoint W u
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint X z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) ) -> ( F ` ( R .\/ S ) ) = ( ( F ` R ) .\/ ( F ` S ) ) )

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
    cP
    cQ
    wne
    #
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
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
    wa
    #
    cR
    cS
    c.or
    co
    #
    cF
    cfv
    #
    cR
    cF
    cfv
    #
    @6
    cW
    c.an
    co
    #
    c.or
    co
    #
    @8
    cS
    cF
    cfv
    c.or
    co
    @5
    @0
    @2
    @3
    @1
    @7
    @10
    wceq
    @0
    @4
    simpl
    @0
    @1
    @2
    @3
    simpr2
    @0
    @1
    @2
    @3
    simpr3
    @0
    @1
    @2
    @3
    simpr1
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
    cS
    cU
    cE
    cF
    cG
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    cO
    @9
    cW
    vs
    cdleme41.b
    cdleme41.l
    cdleme41.j
    cdleme41.m
    cdleme41.a
    cdleme41.h
    cdleme41.u
    cdleme41.d
    cdleme41.e
    cdleme41.g
    cdleme41.i
    cdleme41.n
    cdleme41.o
    cdleme41.f
    @9
    eqid
    #
    cdleme42g
    syl121anc
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
    cS
    cU
    cE
    cF
    cG
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    cO
    @9
    cW
    vs
    cdleme41.b
    cdleme41.l
    cdleme41.j
    cdleme41.m
    cdleme41.a
    cdleme41.h
    cdleme41.u
    cdleme41.d
    cdleme41.e
    cdleme41.g
    cdleme41.i
    cdleme41.n
    cdleme41.o
    cdleme41.f
    @11
    cdleme42ke
    eqtr4d
end
