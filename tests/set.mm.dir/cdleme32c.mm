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
include "simp33.mm"
include "clat.mm"
include "wi.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp21.mm"
include "simp22.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmlem1.mm"
include "syl13anc.mm"
include "mpd.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "simp12.mm"
include "simp13.mm"
include "simp31.mm"
include "simp23l.mm"
include "cdleme27cl.mm"
include "syl222anc.mm"
include "latjlej2.mm"
include "simp1.mm"
include "simp23.mm"
include "simp32.mm"
include "cdleme32a.mm"
include "syl122anc.mm"
include "cdleme32b.mm"
include "3brtr4d.mm"

theorem cdleme32c
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( X e. B /\ Y e. B /\ ( P =/= Q /\ -. X .<_ W ) ) /\ ( ( s e. A /\ -. s .<_ W ) /\ ( s .\/ ( X ./\ W ) ) = X /\ X .<_ Y ) ) -> ( F ` X ) .<_ ( F ` Y ) )

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
    @12
    cW
    c.le
    wbr
    wn
    wa
    #
    @12
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
    cX
    cY
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    cN
    @14
    c.or
    co
    #
    cN
    cY
    cW
    c.an
    co
    #
    c.or
    co
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    c.le
    @18
    @14
    @20
    c.le
    wbr
    #
    @19
    @21
    c.le
    wbr
    #
    @18
    @16
    @23
    @5
    @11
    @13
    @15
    @16
    simp33
    @18
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
    @16
    @23
    wi
    @18
    @0
    @25
    @0
    @1
    @3
    @4
    @11
    @17
    simp11l
    #
    cK
    hllat
    syl
    #
    @5
    @6
    @7
    @10
    @17
    simp21
    #
    @5
    @6
    @7
    @10
    @17
    simp22
    #
    @18
    @1
    @26
    @0
    @1
    @3
    @4
    @11
    @17
    simp11r
    #
    cB
    cH
    cK
    cW
    cdleme32.b
    cdleme32.h
    lhpbase
    syl
    #
    cB
    cK
    c.le
    c.an
    cX
    cY
    cW
    cdleme32.b
    cdleme32.l
    cdleme32.m
    latmlem1
    syl13anc
    mpd
    @18
    @25
    @14
    cB
    wcel
    #
    @20
    cB
    wcel
    #
    cN
    cB
    wcel
    #
    @23
    @24
    wi
    @28
    @18
    @25
    @6
    @26
    @33
    @28
    @29
    @32
    cB
    cK
    c.an
    cX
    cW
    cdleme32.b
    cdleme32.m
    latmcl
    syl3anc
    @18
    @25
    @7
    @26
    @34
    @28
    @30
    @32
    cB
    cK
    c.an
    cY
    cW
    cdleme32.b
    cdleme32.m
    latmcl
    syl3anc
    @18
    @0
    @1
    @3
    @4
    @13
    @8
    @35
    @27
    @31
    @2
    @3
    @4
    @11
    @17
    simp12
    @2
    @3
    @4
    @11
    @17
    simp13
    @5
    @11
    @13
    @15
    @16
    simp31
    #
    @8
    @9
    @6
    @7
    @5
    @17
    simp23l
    vt
    vy
    cA
    cB
    cN
    cI
    cP
    cQ
    cU
    cC
    cH
    c.or
    cK
    c.le
    c.an
    cE
    cW
    cD
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
    cdleme27cl
    syl222anc
    cB
    c.or
    cK
    c.le
    @14
    @20
    cN
    cdleme32.b
    cdleme32.l
    cdleme32.j
    latjlej2
    syl13anc
    mpd
    @18
    @5
    @6
    @10
    @13
    @15
    @22
    @19
    wceq
    @5
    @11
    @17
    simp1
    @29
    @5
    @6
    @7
    @10
    @17
    simp23
    @36
    @5
    @11
    @13
    @15
    @16
    simp32
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
    cX
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
    cX
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
    cdleme32b
    3brtr4d
end
