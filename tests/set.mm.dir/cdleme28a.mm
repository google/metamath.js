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
include "simp23.mm"
include "simp11.mm"
include "3jca.mm"
include "simp33.mm"
include "simp31.mm"
include "simp32l.mm"
include "simp32r.mm"
include "cdleme23b.mm"
include "syl3anc.mm"
include "atbase.mm"
include "latjcl.mm"
include "simp33l.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "cdleme23c.mm"
include "jca.mm"
include "cdleme23a.mm"
include "cdleme27a.mm"
include "syl332anc.mm"
include "simp22l.mm"
include "simp23l.mm"
include "hlatjcl.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "wi.mm"
include "latjlej2.mm"
include "syl13anc.mm"
include "mpd.mm"
include "lattrd.mm"
include "latlej2.mm"
include "wb.mm"
include "latjle12.mm"
include "mpbi2and.mm"

theorem cdleme28a
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
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vs: setvar s
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
  assume cdleme28a.v: |- V = ( ( s .\/ t ) ./\ ( X ./\ W ) )

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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( s e. A /\ -. s .<_ W ) /\ ( t e. A /\ -. t .<_ W ) ) /\ ( s =/= t /\ ( ( s .\/ ( X ./\ W ) ) = X /\ ( t .\/ ( X ./\ W ) ) = X ) /\ ( X e. B /\ -. X .<_ W ) ) ) -> ( C .\/ ( X ./\ W ) ) .<_ ( Y .\/ ( X ./\ W ) ) )

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
    #
    @7
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    vt
    cv
    #
    cA
    wcel
    #
    @11
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    @7
    @11
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
    @11
    @17
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
    cC
    cY
    @17
    c.or
    co
    #
    c.le
    wbr
    #
    @17
    @26
    c.le
    wbr
    #
    cC
    @17
    c.or
    co
    @26
    c.le
    wbr
    #
    @25
    cB
    cK
    c.le
    cC
    cY
    cV
    c.or
    co
    #
    @26
    cdleme26.b
    cdleme26.l
    @25
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @3
    @4
    @15
    @24
    simp11l
    #
    cK
    hllat
    syl
    #
    @25
    @0
    @1
    @3
    @4
    @10
    @6
    cC
    cB
    wcel
    #
    @32
    @0
    @1
    @3
    @4
    @15
    @24
    simp11r
    #
    @2
    @3
    @4
    @15
    @24
    simp12
    #
    @2
    @3
    @4
    @15
    @24
    simp13
    #
    @5
    @6
    @10
    @14
    @24
    simp22
    #
    @5
    @6
    @10
    @14
    @24
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
    #
    @25
    @31
    cY
    cB
    wcel
    #
    cV
    cB
    wcel
    #
    @30
    cB
    wcel
    @33
    @25
    @0
    @1
    @3
    @4
    @14
    @6
    @41
    @32
    @35
    @36
    @37
    @5
    @6
    @10
    @14
    @24
    simp23
    #
    @39
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
    #
    @25
    cV
    cA
    wcel
    #
    @42
    @25
    @2
    @10
    @14
    w3a
    #
    @23
    @16
    @18
    @19
    w3a
    #
    @45
    @25
    @2
    @10
    @14
    @2
    @3
    @4
    @15
    @24
    simp11
    #
    @38
    @43
    3jca
    #
    @5
    @15
    @16
    @20
    @23
    simp33
    #
    @25
    @16
    @18
    @19
    @5
    @15
    @16
    @20
    @23
    simp31
    #
    @18
    @19
    @16
    @23
    @5
    @15
    simp32l
    @18
    @19
    @16
    @23
    @5
    @15
    simp32r
    3jca
    #
    cA
    cB
    @7
    @11
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cX
    cdleme26.b
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme28a.v
    cdleme23b
    syl3anc
    #
    cA
    cB
    cV
    cK
    cdleme26.b
    cdleme26.a
    atbase
    syl
    #
    cB
    c.or
    cK
    cY
    cV
    cdleme26.b
    cdleme26.j
    latjcl
    syl3anc
    @25
    @31
    @41
    @17
    cB
    wcel
    #
    @26
    cB
    wcel
    #
    @33
    @44
    @25
    @31
    @21
    cW
    cB
    wcel
    #
    @55
    @33
    @21
    @22
    @16
    @20
    @5
    @15
    simp33l
    @25
    @1
    @57
    @35
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
    cY
    @17
    cdleme26.b
    cdleme26.j
    latjcl
    syl3anc
    #
    @25
    @2
    @6
    @10
    @3
    @4
    @14
    @16
    @7
    @11
    cV
    c.or
    co
    c.le
    wbr
    #
    wa
    @45
    cV
    cW
    c.le
    wbr
    #
    wa
    cC
    @30
    c.le
    wbr
    @48
    @39
    @38
    @36
    @37
    @43
    @25
    @16
    @60
    @51
    @25
    @46
    @23
    @47
    @60
    @49
    @50
    @52
    cA
    cB
    @7
    @11
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cX
    cdleme26.b
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme28a.v
    cdleme23c
    syl3anc
    jca
    @25
    @45
    @61
    @53
    @25
    @46
    @23
    @47
    @61
    @49
    @50
    @52
    cA
    cB
    @7
    @11
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cX
    cdleme26.b
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme28a.v
    cdleme23a
    syl3anc
    jca
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
    @25
    cV
    @17
    c.le
    wbr
    #
    @30
    @26
    c.le
    wbr
    #
    @25
    cV
    @7
    @11
    c.or
    co
    #
    @17
    c.an
    co
    #
    @17
    c.le
    cdleme28a.v
    @25
    @31
    @64
    cB
    wcel
    #
    @55
    @65
    @17
    c.le
    wbr
    @33
    @25
    @0
    @8
    @12
    @66
    @32
    @8
    @9
    @6
    @14
    @5
    @24
    simp22l
    @12
    @13
    @6
    @10
    @5
    @24
    simp23l
    cA
    cB
    c.or
    cK
    @7
    @11
    cdleme26.b
    cdleme26.j
    cdleme26.a
    hlatjcl
    syl3anc
    @58
    cB
    cK
    c.le
    c.an
    @64
    @17
    cdleme26.b
    cdleme26.l
    cdleme26.m
    latmle2
    syl3anc
    syl5eqbr
    @25
    @31
    @42
    @55
    @41
    @62
    @63
    wi
    @33
    @54
    @58
    @44
    cB
    c.or
    cK
    c.le
    cV
    @17
    cY
    cdleme26.b
    cdleme26.l
    cdleme26.j
    latjlej2
    syl13anc
    mpd
    lattrd
    @25
    @31
    @41
    @55
    @28
    @33
    @44
    @58
    cB
    c.or
    cK
    c.le
    cY
    @17
    cdleme26.b
    cdleme26.l
    cdleme26.j
    latlej2
    syl3anc
    @25
    @31
    @34
    @55
    @56
    @27
    @28
    wa
    @29
    wb
    @33
    @40
    @58
    @59
    cB
    c.or
    cK
    c.le
    cC
    @17
    @26
    cdleme26.b
    cdleme26.l
    cdleme26.j
    latjle12
    syl13anc
    mpbi2and
end
