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
include "simp1.mm"
include "simp22.mm"
include "simp23.mm"
include "simp21.mm"
include "cdleme42i.mm"
include "syl121anc.mm"
include "wb.mm"
include "simp11l.mm"
include "cdleme32fvaw.mm"
include "simpld.mm"
include "syl2anc.mm"
include "cdleme41fva11.mm"
include "simp11r.mm"
include "simp22l.mm"
include "simp22r.mm"
include "simp23l.mm"
include "simp3.mm"
include "cdleme0a.mm"
include "syl222anc.mm"
include "ps-1.mm"
include "syl132anc.mm"
include "mpbid.mm"

theorem cdleme42k
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ R =/= S ) -> ( ( F ` R ) .\/ ( F ` S ) ) = ( ( F ` R ) .\/ V ) )

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
    #
    cS
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cR
    cS
    wne
    #
    w3a
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
    @15
    cV
    c.or
    co
    #
    c.le
    wbr
    #
    @17
    @18
    wceq
    #
    @14
    @4
    @8
    @11
    @5
    @19
    @4
    @12
    @13
    simp1
    #
    @4
    @5
    @8
    @11
    @13
    simp22
    #
    @4
    @5
    @8
    @11
    @13
    simp23
    #
    @4
    @5
    @8
    @11
    @13
    simp21
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
    cdleme42i
    syl121anc
    @14
    @0
    @15
    cA
    wcel
    #
    @16
    cA
    wcel
    #
    @15
    @16
    wne
    @24
    cV
    cA
    wcel
    #
    @19
    @20
    wb
    @0
    @1
    @2
    @3
    @12
    @13
    simp11l
    #
    @14
    @4
    @8
    @24
    @21
    @22
    @4
    @8
    wa
    @24
    @15
    cW
    c.le
    wbr
    wn
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
    simpld
    syl2anc
    #
    @14
    @4
    @11
    @25
    @21
    @23
    @4
    @11
    wa
    @25
    @16
    cW
    c.le
    wbr
    wn
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
    cS
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
    simpld
    syl2anc
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
    cdleme41fva11
    @28
    @14
    @0
    @1
    @6
    @7
    @9
    @13
    @26
    @27
    @0
    @1
    @2
    @3
    @12
    @13
    simp11r
    @6
    @7
    @5
    @11
    @4
    @13
    simp22l
    @6
    @7
    @5
    @11
    @4
    @13
    simp22r
    @9
    @10
    @5
    @8
    @4
    @13
    simp23l
    @4
    @12
    @13
    simp3
    cA
    cR
    cS
    cV
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme41.l
    cdleme41.j
    cdleme41.m
    cdleme41.a
    cdleme41.h
    cdleme34e.v
    cdleme0a
    syl222anc
    cA
    @15
    @16
    @15
    cV
    c.or
    cK
    c.le
    cdleme41.l
    cdleme41.j
    cdleme41.a
    ps-1
    syl132anc
    mpbid
end
