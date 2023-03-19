include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "cdleme27b.mm"
include "adantl.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp11r.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23.mm"
include "simp12.mm"
include "cdleme27cl.mm"
include "syl222anc.mm"
include "simp3rl.mm"
include "atbase.mm"
include "latlej1.mm"
include "syl3anc.mm"
include "adantr.mm"
include "eqbrtrd.mm"
include "simpl11.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl23.mm"
include "simpr.mm"
include "simpl3l.mm"
include "jca.mm"
include "simpl3r.mm"
include "cdleme27a.mm"
include "syl332anc.mm"
include "pm2.61dane.mm"

theorem cdleme27N
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
  let cV: class V
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vs: setvar s
  let cX: class X
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
  disjoint V z
  disjoint W s
  disjoint W t
  disjoint W u
  disjoint W z
  disjoint X s
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ P =/= Q /\ ( s e. A /\ -. s .<_ W ) ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( t e. A /\ -. t .<_ W ) ) /\ ( s .<_ ( t .\/ V ) /\ ( V e. A /\ V .<_ W ) ) ) -> C .<_ ( Y .\/ V ) )

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
    cQ
    wne
    #
    vs
    cv
    #
    cA
    wcel
    @4
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
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
    vt
    cv
    #
    cA
    wcel
    @9
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    @4
    @9
    cV
    c.or
    co
    c.le
    wbr
    #
    cV
    cA
    wcel
    #
    cV
    cW
    c.le
    wbr
    #
    wa
    #
    wa
    #
    w3a
    #
    cC
    cY
    cV
    c.or
    co
    #
    c.le
    wbr
    #
    @4
    @9
    @17
    @4
    @9
    wceq
    #
    wa
    cC
    cY
    @18
    c.le
    @20
    cC
    cY
    wceq
    @17
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
    adantl
    @17
    cY
    @18
    c.le
    wbr
    #
    @20
    @17
    cK
    clat
    wcel
    #
    cY
    cB
    wcel
    #
    cV
    cB
    wcel
    #
    @21
    @17
    @0
    @22
    @0
    @1
    @3
    @5
    @11
    @16
    simp11l
    #
    cK
    hllat
    syl
    @17
    @0
    @1
    @7
    @8
    @10
    @3
    @23
    @25
    @0
    @1
    @3
    @5
    @11
    @16
    simp11r
    @6
    @7
    @8
    @10
    @16
    simp21
    @6
    @7
    @8
    @10
    @16
    simp22
    @6
    @7
    @8
    @10
    @16
    simp23
    @2
    @3
    @5
    @11
    @16
    simp12
    vz
    vu
    cA
    cB
    cY
    cE
    cP
    cQ
    cU
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cO
    cW
    cZ
    vt
    cdleme26.b
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme27.u
    cdleme27.g
    cdleme27.z
    cdleme27.o
    cdleme27.e
    cdleme27.y
    cdleme27cl
    syl222anc
    @17
    @13
    @24
    @13
    @14
    @12
    @6
    @11
    simp3rl
    cA
    cB
    cV
    cK
    cdleme26.b
    cdleme26.a
    atbase
    syl
    cB
    c.or
    cK
    c.le
    cY
    cV
    cdleme26.b
    cdleme26.l
    cdleme26.j
    latlej1
    syl3anc
    adantr
    eqbrtrd
    @17
    @4
    @9
    wne
    #
    wa
    #
    @2
    @3
    @5
    @7
    @8
    @10
    @26
    @12
    wa
    @15
    @19
    @2
    @3
    @5
    @11
    @16
    @26
    simpl11
    @2
    @3
    @5
    @11
    @16
    @26
    simpl12
    @2
    @3
    @5
    @11
    @16
    @26
    simpl13
    @7
    @8
    @10
    @6
    @16
    @26
    simpl21
    @7
    @8
    @10
    @6
    @16
    @26
    simpl22
    @7
    @8
    @10
    @6
    @16
    @26
    simpl23
    @27
    @26
    @12
    @17
    @26
    simpr
    @12
    @15
    @6
    @11
    @26
    simpl3l
    jca
    @12
    @15
    @6
    @11
    @26
    simpl3r
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
    cV
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
    cdleme27a
    syl332anc
    pm2.61dane
end
