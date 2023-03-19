include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "clat.mm"
include "simpl1l.mm"
include "hllat.mm"
include "syl.mm"
include "simprll.mm"
include "atbase.mm"
include "simprrl.mm"
include "3jca.mm"
include "latjcl.mm"
include "cdleme31id.mm"
include "sylan.mm"
include "3ad2antl2.mm"
include "3ad2antl3.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "wne.mm"
include "simpll.mm"
include "simpr.mm"
include "simplrl.mm"
include "simplrr.mm"
include "cdleme42mN.mm"
include "syl13anc.mm"
include "pm2.61dane.mm"

theorem cdleme42mgN
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) ) -> ( F ` ( R .\/ S ) ) = ( ( F ` R ) .\/ ( F ` S ) ) )

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
    #
    cS
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
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
    cS
    cF
    cfv
    #
    c.or
    co
    #
    wceq
    #
    cP
    cQ
    @12
    cK
    clat
    wcel
    #
    cR
    cB
    wcel
    #
    cS
    cB
    wcel
    #
    w3a
    #
    cP
    cQ
    wceq
    #
    @18
    @12
    @19
    @20
    @21
    @12
    @0
    @19
    @0
    @1
    @2
    @3
    @11
    simpl1l
    cK
    hllat
    syl
    @12
    @5
    @20
    @4
    @5
    @6
    @10
    simprll
    cA
    cB
    cR
    cK
    cdleme41.b
    cdleme41.a
    atbase
    syl
    @12
    @8
    @21
    @4
    @7
    @8
    @9
    simprrl
    cA
    cB
    cS
    cK
    cdleme41.b
    cdleme41.a
    atbase
    syl
    3jca
    @22
    @23
    wa
    #
    @14
    @13
    @17
    @22
    @13
    cB
    wcel
    @23
    @14
    @13
    wceq
    cB
    c.or
    cK
    cR
    cS
    cdleme41.b
    cdleme41.j
    latjcl
    vx
    cB
    cP
    cQ
    cF
    c.le
    cO
    cW
    @13
    cdleme41.f
    cdleme31id
    sylan
    @24
    @15
    cR
    @16
    cS
    c.or
    @20
    @19
    @23
    @15
    cR
    wceq
    @21
    vx
    cB
    cP
    cQ
    cF
    c.le
    cO
    cW
    cR
    cdleme41.f
    cdleme31id
    3ad2antl2
    @21
    @19
    @23
    @16
    cS
    wceq
    @20
    vx
    cB
    cP
    cQ
    cF
    c.le
    cO
    cW
    cS
    cdleme41.f
    cdleme31id
    3ad2antl3
    oveq12d
    eqtr4d
    sylan
    @12
    cP
    cQ
    wne
    #
    wa
    @4
    @25
    @7
    @10
    @18
    @4
    @11
    @25
    simpll
    @12
    @25
    simpr
    @4
    @7
    @10
    @25
    simplrl
    @4
    @7
    @10
    @25
    simplrr
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
    cdleme42mN
    syl13anc
    pm2.61dane
end
