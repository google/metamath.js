include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp1.mm"
include "simp2ll.mm"
include "atbase.mm"
include "cdleme32fvcl.mm"
include "syl2anc.mm"
include "simp2rl.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl5eqel.mm"
include "latlej1.mm"
include "cdleme42h.mm"
include "wb.mm"
include "latjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"

theorem cdleme42i
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ P =/= Q ) -> ( ( F ` R ) .\/ ( F ` S ) ) .<_ ( ( F ` R ) .\/ V ) )

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
    cP
    cQ
    wne
    #
    w3a
    #
    cR
    cF
    cfv
    #
    @14
    cV
    c.or
    co
    #
    c.le
    wbr
    #
    cS
    cF
    cfv
    #
    @15
    c.le
    wbr
    #
    @14
    @17
    c.or
    co
    @15
    c.le
    wbr
    #
    @13
    cK
    clat
    wcel
    #
    @14
    cB
    wcel
    #
    cV
    cB
    wcel
    #
    @16
    @13
    @0
    @20
    @0
    @1
    @2
    @3
    @11
    @12
    simp11l
    #
    cK
    hllat
    syl
    #
    @13
    @4
    cR
    cB
    wcel
    #
    @21
    @4
    @11
    @12
    simp1
    #
    @13
    @5
    @25
    @5
    @6
    @10
    @4
    @12
    simp2ll
    #
    cA
    cB
    cR
    cK
    cdleme41.b
    cdleme41.a
    atbase
    syl
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
    cR
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
    cdleme32fvcl
    syl2anc
    #
    @13
    cV
    cR
    cS
    c.or
    co
    #
    cW
    c.an
    co
    #
    cB
    cdleme34e.v
    @13
    @20
    @29
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @30
    cB
    wcel
    @24
    @13
    @0
    @5
    @8
    @31
    @23
    @27
    @8
    @9
    @7
    @4
    @12
    simp2rl
    #
    cA
    cB
    c.or
    cK
    cR
    cS
    cdleme41.b
    cdleme41.j
    cdleme41.a
    hlatjcl
    syl3anc
    @13
    @1
    @32
    @0
    @1
    @2
    @3
    @11
    @12
    simp11r
    cB
    cH
    cK
    cW
    cdleme41.b
    cdleme41.h
    lhpbase
    syl
    cB
    cK
    c.an
    @29
    cW
    cdleme41.b
    cdleme41.m
    latmcl
    syl3anc
    syl5eqel
    #
    cB
    c.or
    cK
    c.le
    @14
    cV
    cdleme41.b
    cdleme41.l
    cdleme41.j
    latlej1
    syl3anc
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
    cdleme42h
    @13
    @20
    @21
    @17
    cB
    wcel
    #
    @15
    cB
    wcel
    #
    @16
    @18
    wa
    @19
    wb
    @24
    @28
    @13
    @4
    cS
    cB
    wcel
    #
    @35
    @26
    @13
    @8
    @37
    @33
    cA
    cB
    cS
    cK
    cdleme41.b
    cdleme41.a
    atbase
    syl
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
    cS
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
    cdleme32fvcl
    syl2anc
    @13
    @20
    @21
    @22
    @36
    @24
    @28
    @34
    cB
    c.or
    cK
    @14
    cV
    cdleme41.b
    cdleme41.j
    latjcl
    syl3anc
    cB
    c.or
    cK
    c.le
    @14
    @17
    @15
    cdleme41.b
    cdleme41.l
    cdleme41.j
    latjle12
    syl13anc
    mpbi2and
end
