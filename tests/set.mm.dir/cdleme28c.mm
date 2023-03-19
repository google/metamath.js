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
include "cdleme27b.mm"
include "oveq1d.mm"
include "adantl.mm"
include "simpl11.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl23.mm"
include "simpr.mm"
include "simpl31.mm"
include "simpl32.mm"
include "jca.mm"
include "simpl33.mm"
include "cdleme28b.mm"
include "syl333anc.mm"
include "pm2.61dane.mm"

theorem cdleme28c
  let vz: setvar z
  let vu: setvar u
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
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vs: setvar s
  let cV: class V
  assume cdleme26.b: |- B = ( Base ` K )
  assume cdleme26.l: |- .<_ = ( le ` K )
  assume cdleme26.j: |- .\/ = ( join ` K )
  assume cdleme26.m: |- ./\ = ( meet ` K )
  assume cdleme26.a: |- A = ( Atoms ` K )
  assume cdleme26.h: |- H = ( LHyp ` K )
  assume cdleme27.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme27.f: |- F = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdleme27.z: |- Z = ( ( z .\/ U ) ./\ ( Q .\/ ( ( P .\/ z ) ./\ W ) ) )
  assume cdleme27.n: |- N = ( ( P .\/ Q ) ./\ ( Z .\/ ( ( s .\/ z ) ./\ W ) ) )
  assume cdleme27.d: |- D = ( iota_ u e. B A. z e. A ( ( -. z .<_ W /\ -. z .<_ ( P .\/ Q ) ) -> u = N ) )
  assume cdleme27.c: |- C = if ( s .<_ ( P .\/ Q ) , D , F )
  assume cdleme27.g: |- G = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdleme27.o: |- O = ( ( P .\/ Q ) ./\ ( Z .\/ ( ( t .\/ z ) ./\ W ) ) )
  assume cdleme27.e: |- E = ( iota_ u e. B A. z e. A ( ( -. z .<_ W /\ -. z .<_ ( P .\/ Q ) ) -> u = O ) )
  assume cdleme27.y: |- Y = if ( t .<_ ( P .\/ Q ) , E , G )

  disjoint X z
  disjoint X t
  disjoint s t
  disjoint s u
  disjoint s z
  disjoint A s
  disjoint t u
  disjoint t z
  disjoint A t
  disjoint u z
  disjoint A u
  disjoint A z
  disjoint B s
  disjoint B t
  disjoint B u
  disjoint B z
  disjoint F u
  disjoint G u
  disjoint H s
  disjoint H t
  disjoint H z
  disjoint .\/ s
  disjoint .\/ t
  disjoint .\/ u
  disjoint .\/ z
  disjoint K s
  disjoint K t
  disjoint K z
  disjoint .<_ s
  disjoint .<_ t
  disjoint .<_ u
  disjoint .<_ z
  disjoint ./\ s
  disjoint ./\ t
  disjoint ./\ u
  disjoint ./\ z
  disjoint N t
  disjoint N u
  disjoint O s
  disjoint O u
  disjoint P s
  disjoint P t
  disjoint P u
  disjoint P z
  disjoint Q s
  disjoint Q t
  disjoint Q u
  disjoint Q z
  disjoint U s
  disjoint U t
  disjoint U u
  disjoint U z
  disjoint W s
  disjoint W t
  disjoint W u
  disjoint W z
  disjoint X s
  disjoint V z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( s e. A /\ -. s .<_ W ) /\ ( t e. A /\ -. t .<_ W ) ) /\ ( ( s .\/ ( X ./\ W ) ) = X /\ ( t .\/ ( X ./\ W ) ) = X /\ ( X e. B /\ -. X .<_ W ) ) ) -> ( C .\/ ( X ./\ W ) ) = ( Y .\/ ( X ./\ W ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    vs
    cv
    #
    cA
    wcel
    @5
    cW
    c.le
    wbr
    wn
    wa
    #
    vt
    cv
    #
    cA
    wcel
    @7
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    @5
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
    @7
    @10
    c.or
    co
    cX
    wceq
    #
    cX
    cB
    wcel
    cX
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    w3a
    #
    cC
    @10
    c.or
    co
    cY
    @10
    c.or
    co
    wceq
    #
    @5
    @7
    @5
    @7
    wceq
    #
    @16
    @15
    @17
    cC
    cY
    @10
    c.or
    vz
    vu
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
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    cY
    cZ
    vs
    cdleme26.b
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme27.u
    cdleme27.f
    cdleme27.z
    cdleme27.n
    cdleme27.d
    cdleme27.c
    cdleme27.g
    cdleme27.o
    cdleme27.e
    cdleme27.y
    cdleme27b
    oveq1d
    adantl
    @15
    @5
    @7
    wne
    #
    wa
    #
    @0
    @1
    @2
    @4
    @6
    @8
    @18
    @11
    @12
    wa
    @13
    @16
    @0
    @1
    @2
    @9
    @14
    @18
    simpl11
    @0
    @1
    @2
    @9
    @14
    @18
    simpl12
    @0
    @1
    @2
    @9
    @14
    @18
    simpl13
    @4
    @6
    @8
    @3
    @14
    @18
    simpl21
    @4
    @6
    @8
    @3
    @14
    @18
    simpl22
    @4
    @6
    @8
    @3
    @14
    @18
    simpl23
    @15
    @18
    simpr
    @19
    @11
    @12
    @11
    @12
    @13
    @3
    @9
    @18
    simpl31
    @11
    @12
    @13
    @3
    @9
    @18
    simpl32
    jca
    @11
    @12
    @13
    @3
    @9
    @18
    simpl33
    vz
    vu
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
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    cX
    cY
    cZ
    vs
    cdleme26.b
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme27.u
    cdleme27.f
    cdleme27.z
    cdleme27.n
    cdleme27.d
    cdleme27.c
    cdleme27.g
    cdleme27.o
    cdleme27.e
    cdleme27.y
    cdleme28b
    syl333anc
    pm2.61dane
end
