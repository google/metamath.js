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
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp11r.mm"
include "simp12.mm"
include "simp13.mm"
include "simp22.mm"
include "simp21.mm"
include "cdleme27cl.mm"
include "syl222anc.mm"
include "simp33l.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latjcl.mm"
include "simp23.mm"
include "eqid.mm"
include "cdleme28a.mm"
include "simp11.mm"
include "simp31.mm"
include "necomd.mm"
include "simp32.mm"
include "ancomd.mm"
include "simp33.mm"
include "syl333anc.mm"
include "latasymd.mm"

theorem cdleme28b
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( s e. A /\ -. s .<_ W ) /\ ( t e. A /\ -. t .<_ W ) ) /\ ( s =/= t /\ ( ( s .\/ ( X ./\ W ) ) = X /\ ( t .\/ ( X ./\ W ) ) = X ) /\ ( X e. B /\ -. X .<_ W ) ) ) -> ( C .\/ ( X ./\ W ) ) = ( Y .\/ ( X ./\ W ) ) )

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
    vs
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
    @7
    @9
    wne
    #
    @7
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
    @9
    @13
    c.or
    co
    cX
    wceq
    #
    wa
    #
    cX
    cB
    wcel
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
    w3a
    #
    cB
    cK
    c.le
    cC
    @13
    c.or
    co
    #
    cY
    @13
    c.or
    co
    #
    cdleme26.b
    cdleme26.l
    @21
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @3
    @4
    @11
    @20
    simp11l
    #
    cK
    hllat
    syl
    #
    @21
    @24
    cC
    cB
    wcel
    #
    @13
    cB
    wcel
    #
    @22
    cB
    wcel
    @26
    @21
    @0
    @1
    @3
    @4
    @8
    @6
    @27
    @25
    @0
    @1
    @3
    @4
    @11
    @20
    simp11r
    #
    @2
    @3
    @4
    @11
    @20
    simp12
    #
    @2
    @3
    @4
    @11
    @20
    simp13
    #
    @5
    @6
    @8
    @10
    @20
    simp22
    #
    @5
    @6
    @8
    @10
    @20
    simp21
    #
    vz
    vu
    cA
    cB
    cC
    cD
    cP
    cQ
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
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
    cdleme27cl
    syl222anc
    @21
    @24
    @17
    cW
    cB
    wcel
    #
    @28
    @26
    @17
    @18
    @12
    @16
    @5
    @11
    simp33l
    @21
    @1
    @34
    @29
    cB
    cH
    cK
    cW
    cdleme26.b
    cdleme26.h
    lhpbase
    syl
    cB
    cK
    c.an
    cX
    cW
    cdleme26.b
    cdleme26.m
    latmcl
    syl3anc
    #
    cB
    c.or
    cK
    cC
    @13
    cdleme26.b
    cdleme26.j
    latjcl
    syl3anc
    @21
    @24
    cY
    cB
    wcel
    #
    @28
    @23
    cB
    wcel
    @26
    @21
    @0
    @1
    @3
    @4
    @10
    @6
    @36
    @25
    @29
    @30
    @31
    @5
    @6
    @8
    @10
    @20
    simp23
    #
    @33
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
    @35
    cB
    c.or
    cK
    cY
    @13
    cdleme26.b
    cdleme26.j
    latjcl
    syl3anc
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
    @7
    @9
    c.or
    co
    @13
    c.an
    co
    #
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
    @38
    eqid
    cdleme28a
    @21
    @2
    @3
    @4
    @6
    @10
    @8
    @9
    @7
    wne
    @15
    @14
    wa
    @19
    @23
    @22
    c.le
    wbr
    @2
    @3
    @4
    @11
    @20
    simp11
    @30
    @31
    @33
    @37
    @32
    @21
    @7
    @9
    @5
    @11
    @12
    @16
    @19
    simp31
    necomd
    @21
    @14
    @15
    @5
    @11
    @12
    @16
    @19
    simp32
    ancomd
    @5
    @11
    @12
    @16
    @19
    simp33
    vz
    vu
    vs
    cA
    cB
    cY
    cE
    cP
    cQ
    cU
    cD
    cG
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cO
    cN
    @9
    @7
    c.or
    co
    @13
    c.an
    co
    #
    cW
    cX
    cC
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
    cdleme27.f
    cdleme27.n
    cdleme27.d
    cdleme27.c
    @39
    eqid
    cdleme28a
    syl333anc
    latasymd
end
