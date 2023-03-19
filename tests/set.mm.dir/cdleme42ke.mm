include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "simpl1l.mm"
include "simpr2.mm"
include "cdleme32fvaw.mm"
include "syldan.mm"
include "simpld.mm"
include "hlatjidm.mm"
include "syl2anc.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "sylan9req.mm"
include "cp0.mm"
include "simpr2l.mm"
include "oveq1d.mm"
include "simpl1.mm"
include "eqid.mm"
include "lhpmat.mm"
include "eqtrd.mm"
include "col.mm"
include "hlol.mm"
include "syl.mm"
include "atbase.mm"
include "olj01.mm"
include "oveq2.mm"
include "syl6eqr.mm"
include "eqtr3d.mm"
include "cdleme42k.mm"
include "3expa.mm"
include "pm2.61dane.mm"

theorem cdleme42ke
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
  let cV: class V
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
  assume cdleme34e.v: |- V = ( ( R .\/ S ) ./\ W )

  disjoint V s
  disjoint V t
  disjoint V x
  disjoint V z
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint S s
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint S t
  disjoint x y
  disjoint x z
  disjoint S x
  disjoint y z
  disjoint S y
  disjoint S z
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) ) -> ( ( F ` R ) .\/ ( F ` S ) ) = ( ( F ` R ) .\/ V ) )

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
    @13
    cV
    c.or
    co
    #
    wceq
    #
    cR
    cS
    @12
    cR
    cS
    wceq
    #
    wa
    @13
    @15
    @16
    @12
    @18
    @13
    @13
    @13
    c.or
    co
    #
    @15
    @12
    @0
    @13
    cA
    wcel
    #
    @19
    @13
    wceq
    @0
    @1
    @3
    @4
    @11
    simpl1l
    #
    @12
    @20
    @13
    cW
    c.le
    wbr
    wn
    #
    @5
    @11
    @9
    @20
    @22
    wa
    @5
    @6
    @9
    @10
    simpr2
    #
    vx
    vy
    vz
    vt
    cA
    cB
    cD
    cE
    cP
    cQ
    cR
    cU
    cG
    cF
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
    cdleme32fvaw
    syldan
    simpld
    #
    cA
    c.or
    cK
    @13
    cdleme41.j
    cdleme41.a
    hlatjidm
    syl2anc
    @18
    @13
    @14
    @13
    c.or
    cR
    cS
    cF
    fveq2
    oveq2d
    sylan9req
    @12
    @18
    @13
    @13
    cR
    cR
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    @16
    @12
    @27
    @13
    cK
    cp0
    cfv
    #
    c.or
    co
    #
    @13
    @12
    @26
    @28
    @13
    c.or
    @12
    @26
    cR
    cW
    c.an
    co
    #
    @28
    @12
    @25
    cR
    cW
    c.an
    @12
    @0
    @7
    @25
    cR
    wceq
    @21
    @7
    @8
    @6
    @10
    @5
    simpr2l
    cA
    c.or
    cK
    cR
    cdleme41.j
    cdleme41.a
    hlatjidm
    syl2anc
    oveq1d
    @12
    @2
    @9
    @30
    @28
    wceq
    @2
    @3
    @4
    @11
    simpl1
    @23
    cA
    cR
    cH
    cK
    c.le
    c.an
    cW
    @28
    cdleme41.l
    cdleme41.m
    @28
    eqid
    #
    cdleme41.a
    cdleme41.h
    lhpmat
    syl2anc
    eqtrd
    oveq2d
    @12
    cK
    col
    wcel
    #
    @13
    cB
    wcel
    #
    @29
    @13
    wceq
    @12
    @0
    @32
    @21
    cK
    hlol
    syl
    @12
    @20
    @33
    @24
    cA
    cB
    @13
    cK
    cdleme41.b
    cdleme41.a
    atbase
    syl
    cB
    c.or
    cK
    @13
    @28
    cdleme41.b
    cdleme41.j
    @31
    olj01
    syl2anc
    eqtrd
    @18
    @26
    cV
    @13
    c.or
    @18
    @26
    cR
    cS
    c.or
    co
    #
    cW
    c.an
    co
    cV
    @18
    @25
    @34
    cW
    c.an
    cR
    cS
    cR
    c.or
    oveq2
    oveq1d
    cdleme34e.v
    syl6eqr
    oveq2d
    sylan9req
    eqtr3d
    @5
    @11
    cR
    cS
    wne
    @17
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
    cV
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
    cdleme34e.v
    cdleme42k
    3expa
    pm2.61dane
end
