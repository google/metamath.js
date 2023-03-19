include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "simp1.mm"
include "simp22.mm"
include "simp23l.mm"
include "simp23r.mm"
include "simp33.mm"
include "clat.mm"
include "wi.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp21.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "lattr.mm"
include "syl13anc.mm"
include "mpand.mm"
include "mtod.mm"
include "jca.mm"
include "simp31.mm"
include "simp11.mm"
include "simp31l.mm"
include "simp32.mm"
include "cdleme30a.mm"
include "syl132anc.mm"
include "cdleme32a.mm"
include "syl122anc.mm"

theorem cdleme32b
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let cR: class R
  assume cdleme32.b: |- B = ( Base ` K )
  assume cdleme32.l: |- .<_ = ( le ` K )
  assume cdleme32.j: |- .\/ = ( join ` K )
  assume cdleme32.m: |- ./\ = ( meet ` K )
  assume cdleme32.a: |- A = ( Atoms ` K )
  assume cdleme32.h: |- H = ( LHyp ` K )
  assume cdleme32.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme32.c: |- C = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdleme32.d: |- D = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdleme32.e: |- E = ( ( P .\/ Q ) ./\ ( D .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdleme32.i: |- I = ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = E ) )
  assume cdleme32.n: |- N = if ( s .<_ ( P .\/ Q ) , I , C )
  assume cdleme32.o: |- O = ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( N .\/ ( x ./\ W ) ) ) )
  assume cdleme32.f: |- F = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , O , x ) )

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
  disjoint C y
  disjoint D s
  disjoint D y
  disjoint D z
  disjoint E y
  disjoint H s
  disjoint H t
  disjoint .\/ s
  disjoint .\/ t
  disjoint .\/ x
  disjoint .\/ y
  disjoint .\/ z
  disjoint K s
  disjoint K t
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
  disjoint N x
  disjoint N z
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
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint X z
  disjoint H y
  disjoint K y
  disjoint Y y
  disjoint H z
  disjoint K z
  disjoint Y s
  disjoint Y t
  disjoint Y x
  disjoint Y z
  disjoint R s
  disjoint R t
  disjoint R y
  disjoint R x
  disjoint R z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( X e. B /\ Y e. B /\ ( P =/= Q /\ -. X .<_ W ) ) /\ ( ( s e. A /\ -. s .<_ W ) /\ ( s .\/ ( X ./\ W ) ) = X /\ X .<_ Y ) ) -> ( F ` Y ) = ( N .\/ ( Y ./\ W ) ) )

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
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cP
    cQ
    wne
    #
    cX
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    w3a
    #
    vs
    cv
    #
    cA
    wcel
    #
    @13
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    @13
    cX
    cW
    c.an
    co
    c.or
    co
    cX
    wceq
    #
    cX
    cY
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    @5
    @7
    @8
    cY
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    @16
    @13
    cY
    cW
    c.an
    co
    #
    c.or
    co
    cY
    wceq
    #
    cY
    cF
    cfv
    cN
    @23
    c.or
    co
    wceq
    @5
    @12
    @19
    simp1
    @5
    @6
    @7
    @11
    @19
    simp22
    #
    @20
    @8
    @22
    @8
    @10
    @6
    @7
    @5
    @19
    simp23l
    @20
    @21
    @9
    @8
    @10
    @6
    @7
    @5
    @19
    simp23r
    #
    @20
    @18
    @21
    @9
    @5
    @12
    @16
    @17
    @18
    simp33
    #
    @20
    cK
    clat
    wcel
    #
    @6
    @7
    cW
    cB
    wcel
    #
    @18
    @21
    wa
    @9
    wi
    @20
    @0
    @28
    @0
    @1
    @3
    @4
    @12
    @19
    simp11l
    cK
    hllat
    syl
    @5
    @6
    @7
    @11
    @19
    simp21
    #
    @25
    @20
    @1
    @29
    @0
    @1
    @3
    @4
    @12
    @19
    simp11r
    cB
    cH
    cK
    cW
    cdleme32.b
    cdleme32.h
    lhpbase
    syl
    cB
    cK
    c.le
    cX
    cY
    cW
    cdleme32.b
    cdleme32.l
    lattr
    syl13anc
    mpand
    mtod
    jca
    @5
    @12
    @16
    @17
    @18
    simp31
    @20
    @2
    @14
    @6
    @10
    wa
    @7
    @17
    @18
    @24
    @2
    @3
    @4
    @12
    @19
    simp11
    @14
    @15
    @17
    @18
    @5
    @12
    simp31l
    @20
    @6
    @10
    @30
    @26
    jca
    @25
    @5
    @12
    @16
    @17
    @18
    simp32
    @27
    cA
    cB
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    cY
    vs
    cdleme32.b
    cdleme32.l
    cdleme32.j
    cdleme32.m
    cdleme32.a
    cdleme32.h
    cdleme30a
    syl132anc
    vx
    vy
    vz
    vt
    cA
    cB
    cC
    cD
    cP
    cQ
    cU
    cE
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
    cY
    vs
    cdleme32.b
    cdleme32.l
    cdleme32.j
    cdleme32.m
    cdleme32.a
    cdleme32.h
    cdleme32.u
    cdleme32.c
    cdleme32.d
    cdleme32.e
    cdleme32.i
    cdleme32.n
    cdleme32.o
    cdleme32.f
    cdleme32a
    syl122anc
end
