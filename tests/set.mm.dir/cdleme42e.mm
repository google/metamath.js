include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "csb.mm"
include "simp1.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2ll.mm"
include "atbase.mm"
include "simp11.mm"
include "simp2rl.mm"
include "cdleme0aa.mm"
include "syl3anc.mm"
include "latjcl.mm"
include "simp3.mm"
include "simp2l.mm"
include "simp2r.mm"
include "cdleme42c.mm"
include "jca.mm"
include "cdleme42d.mm"
include "cdleme42b.mm"
include "syl122anc.mm"

theorem cdleme42e
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ P =/= Q ) -> ( F ` ( R .\/ V ) ) = ( [_ R / s ]_ N .\/ ( ( R .\/ V ) ./\ W ) ) )

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
    @5
    cR
    cV
    c.or
    co
    #
    cB
    wcel
    #
    @13
    @15
    cW
    c.le
    wbr
    wn
    #
    wa
    @8
    cR
    @15
    cW
    c.an
    co
    #
    c.or
    co
    @15
    wceq
    #
    @15
    cF
    cfv
    vs
    cR
    cN
    csb
    @18
    c.or
    co
    wceq
    @5
    @12
    @13
    simp1
    @14
    cK
    clat
    wcel
    #
    cR
    cB
    wcel
    #
    cV
    cB
    wcel
    #
    @16
    @14
    @0
    @20
    @0
    @1
    @3
    @4
    @12
    @13
    simp11l
    cK
    hllat
    syl
    @14
    @6
    @21
    @6
    @7
    @11
    @5
    @13
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
    @14
    @2
    @6
    @9
    @22
    @2
    @3
    @4
    @12
    @13
    simp11
    #
    @23
    @9
    @10
    @8
    @5
    @13
    simp2rl
    cA
    cB
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
    cdleme41.b
    cdleme0aa
    syl3anc
    cB
    c.or
    cK
    cR
    cV
    cdleme41.b
    cdleme41.j
    latjcl
    syl3anc
    @14
    @13
    @17
    @5
    @12
    @13
    simp3
    @14
    @2
    @8
    @11
    @17
    @24
    @5
    @8
    @11
    @13
    simp2l
    #
    @5
    @8
    @11
    @13
    simp2r
    #
    cA
    cB
    cR
    cS
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cdleme41.b
    cdleme41.l
    cdleme41.j
    cdleme41.m
    cdleme41.a
    cdleme41.h
    cdleme34e.v
    cdleme42c
    syl3anc
    jca
    @25
    @14
    @2
    @8
    @11
    @19
    @24
    @25
    @26
    cA
    cB
    cR
    cS
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cdleme41.b
    cdleme41.l
    cdleme41.j
    cdleme41.m
    cdleme41.a
    cdleme41.h
    cdleme34e.v
    cdleme42d
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
    @15
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
    cdleme42b
    syl122anc
end
