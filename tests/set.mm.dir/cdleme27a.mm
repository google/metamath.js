include "cv.mm"
include "co.mm"
include "wbr.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "wn.mm"
include "w3a.mm"
include "wi.mm"
include "wceq.mm"
include "simp211.mm"
include "simp221.mm"
include "simp222.mm"
include "simp213.mm"
include "simp223.mm"
include "simp23r.mm"
include "simp212.mm"
include "simp1l.mm"
include "simp1r.mm"
include "3jca.mm"
include "simp3.mm"
include "cdleme26ee.mm"
include "syl332anc.mm"
include "3expia.mm"
include "simp11l.mm"
include "3ad2ant2.mm"
include "simp13l.mm"
include "simp23l.mm"
include "simp3ll.mm"
include "simp21l.mm"
include "simp22l.mm"
include "simp3rl.mm"
include "simp3lr.mm"
include "cdleme22b.mm"
include "syl232anc.mm"
include "pm2.21dd.mm"
include "pm2.61dne.mm"
include "cif.mm"
include "iftrue.mm"
include "syl5eq.mm"
include "ad2antrr.mm"
include "oveq1d.mm"
include "ad2antlr.mm"
include "3brtr4d.mm"
include "ex.mm"
include "simpr11.mm"
include "simpr12.mm"
include "simpll.mm"
include "jca.mm"
include "simpr23.mm"
include "simpr21.mm"
include "simpr22.mm"
include "simpr13.mm"
include "simplr.mm"
include "simpr3l.mm"
include "simpr3r.mm"
include "eqid.mm"
include "wral.mm"
include "crio.mm"
include "cdleme25cv.mm"
include "cdleme26f.mm"
include "syl333anc.mm"
include "iffalse.mm"
include "cdleme26f2.mm"
include "cdleme22g.mm"
include "syl323anc.mm"
include "4cases.mm"

theorem cdleme27a
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ P =/= Q /\ ( s e. A /\ -. s .<_ W ) ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( t e. A /\ -. t .<_ W ) ) /\ ( ( s =/= t /\ s .<_ ( t .\/ V ) ) /\ ( V e. A /\ V .<_ W ) ) ) -> C .<_ ( Y .\/ V ) )

  proof
    vs
    cv
    #
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    vt
    cv
    #
    @1
    c.le
    wbr
    #
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
    @0
    cA
    wcel
    #
    @0
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cQ
    cA
    wcel
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    @3
    cA
    wcel
    #
    @3
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    @0
    @3
    wne
    #
    @0
    @3
    cV
    c.or
    co
    #
    c.le
    wbr
    #
    wa
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
    wi
    @2
    @4
    wa
    #
    @31
    @33
    @34
    @31
    wa
    #
    cD
    cE
    cV
    c.or
    co
    #
    cC
    @32
    c.le
    @35
    cD
    @36
    c.le
    wbr
    #
    @24
    @1
    @34
    @31
    @24
    @1
    wceq
    #
    @37
    @34
    @31
    @38
    w3a
    #
    @7
    @15
    @18
    @11
    @21
    @29
    @8
    @2
    @4
    w3a
    @38
    @37
    @7
    @8
    @11
    @22
    @30
    @34
    @38
    simp211
    @15
    @18
    @21
    @12
    @30
    @34
    @38
    simp221
    @15
    @18
    @21
    @12
    @30
    @34
    @38
    simp222
    @7
    @8
    @11
    @22
    @30
    @34
    @38
    simp213
    @15
    @18
    @21
    @12
    @30
    @34
    @38
    simp223
    @26
    @29
    @12
    @22
    @34
    @38
    simp23r
    @39
    @8
    @2
    @4
    @7
    @8
    @11
    @22
    @30
    @34
    @38
    simp212
    @2
    @4
    @31
    @38
    simp1l
    @2
    @4
    @31
    @38
    simp1r
    3jca
    @34
    @31
    @38
    simp3
    vz
    vu
    cA
    cB
    cP
    cQ
    @0
    @3
    cU
    cE
    cZ
    cH
    cD
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cV
    cW
    cdleme26.b
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme27.u
    cdleme27.z
    cdleme27.n
    cdleme27.o
    cdleme27.d
    cdleme27.e
    cdleme26ee
    syl332anc
    3expia
    @34
    @31
    @24
    @1
    wne
    #
    @37
    @34
    @31
    @40
    w3a
    #
    @4
    @37
    @2
    @4
    @31
    @40
    simp1r
    @41
    @5
    @9
    @19
    @23
    w3a
    @13
    @16
    @8
    @27
    @40
    @25
    @2
    w3a
    @4
    wn
    #
    @31
    @34
    @5
    @40
    @5
    @6
    @8
    @11
    @22
    @30
    simp11l
    3ad2ant2
    @41
    @9
    @19
    @23
    @31
    @34
    @9
    @40
    @9
    @10
    @7
    @8
    @22
    @30
    simp13l
    3ad2ant2
    @31
    @34
    @19
    @40
    @19
    @20
    @15
    @18
    @12
    @30
    simp23l
    3ad2ant2
    @31
    @34
    @23
    @40
    @23
    @25
    @29
    @12
    @22
    simp3ll
    3ad2ant2
    3jca
    @31
    @34
    @13
    @40
    @13
    @14
    @18
    @21
    @12
    @30
    simp21l
    3ad2ant2
    @31
    @34
    @16
    @40
    @16
    @17
    @15
    @21
    @12
    @30
    simp22l
    3ad2ant2
    @7
    @8
    @11
    @22
    @30
    @34
    @40
    simp212
    @31
    @34
    @27
    @40
    @27
    @28
    @26
    @12
    @22
    simp3rl
    3ad2ant2
    @41
    @40
    @25
    @2
    @34
    @31
    @40
    simp3
    @31
    @34
    @25
    @40
    @23
    @25
    @29
    @12
    @22
    simp3lr
    3ad2ant2
    @2
    @4
    @31
    @40
    simp1l
    3jca
    cA
    cP
    cQ
    @0
    @3
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme22b
    syl232anc
    pm2.21dd
    3expia
    pm2.61dne
    @2
    cC
    cD
    wceq
    #
    @4
    @31
    @2
    cC
    @2
    cD
    cF
    cif
    #
    cD
    cdleme27.c
    @2
    cD
    cF
    iftrue
    syl5eq
    #
    ad2antrr
    @4
    @32
    @36
    wceq
    #
    @2
    @31
    @4
    cY
    cE
    cV
    c.or
    @4
    cY
    @4
    cE
    cG
    cif
    #
    cE
    cdleme27.y
    @4
    cE
    cG
    iftrue
    syl5eq
    oveq1d
    #
    ad2antlr
    3brtr4d
    ex
    @2
    @42
    wa
    #
    @31
    @33
    @49
    @31
    wa
    #
    cD
    cG
    cV
    c.or
    co
    #
    cC
    @32
    c.le
    @50
    @7
    @8
    @2
    wa
    @21
    @15
    @18
    @11
    @42
    @26
    @29
    cD
    @51
    c.le
    wbr
    @7
    @8
    @11
    @22
    @30
    @49
    simpr11
    @50
    @8
    @2
    @7
    @8
    @11
    @22
    @30
    @49
    simpr12
    @2
    @42
    @31
    simpll
    jca
    @15
    @18
    @21
    @12
    @30
    @49
    simpr23
    @15
    @18
    @21
    @12
    @30
    @49
    simpr21
    @15
    @18
    @21
    @12
    @30
    @49
    simpr22
    @7
    @8
    @11
    @22
    @30
    @49
    simpr13
    @2
    @42
    @31
    simplr
    @26
    @29
    @12
    @22
    @49
    simpr3l
    @26
    @29
    @12
    @22
    @49
    simpr3r
    vu
    vt
    cA
    cB
    cP
    cQ
    @0
    cU
    cG
    cH
    cD
    c.or
    cK
    c.le
    c.an
    @1
    cG
    @0
    @3
    c.or
    co
    cW
    c.an
    co
    c.or
    co
    c.an
    co
    #
    cV
    cW
    cdleme26.b
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme27.u
    cdleme27.g
    @52
    eqid
    #
    vt
    vu
    cA
    cB
    cP
    cQ
    @0
    cU
    @20
    @42
    wa
    vu
    cv
    #
    @52
    wceq
    wi
    vt
    cA
    wral
    vu
    cB
    crio
    #
    cZ
    cG
    cD
    c.or
    c.le
    c.an
    cN
    @52
    cW
    vz
    cdleme27.z
    cdleme27.n
    cdleme27.g
    @53
    cdleme27.d
    @55
    eqid
    cdleme25cv
    cdleme26f
    syl333anc
    @2
    @43
    @42
    @31
    @45
    ad2antrr
    @42
    @32
    @51
    wceq
    #
    @2
    @31
    @42
    cY
    cG
    cV
    c.or
    @42
    cY
    @47
    cG
    cdleme27.y
    @4
    cE
    cG
    iffalse
    syl5eq
    oveq1d
    #
    ad2antlr
    3brtr4d
    ex
    @2
    wn
    #
    @4
    wa
    #
    @31
    @33
    @59
    @31
    wa
    #
    cF
    @36
    cC
    @32
    c.le
    @60
    @7
    @8
    @4
    wa
    @11
    @15
    @18
    @21
    @58
    @26
    @29
    cF
    @36
    c.le
    wbr
    @7
    @8
    @11
    @22
    @30
    @59
    simpr11
    @60
    @8
    @4
    @7
    @8
    @11
    @22
    @30
    @59
    simpr12
    @58
    @4
    @31
    simplr
    jca
    @7
    @8
    @11
    @22
    @30
    @59
    simpr13
    @15
    @18
    @21
    @12
    @30
    @59
    simpr21
    @15
    @18
    @21
    @12
    @30
    @59
    simpr22
    @15
    @18
    @21
    @12
    @30
    @59
    simpr23
    @58
    @4
    @31
    simpll
    @26
    @29
    @12
    @22
    @59
    simpr3l
    @26
    @29
    @12
    @22
    @59
    simpr3r
    vu
    cA
    cB
    cP
    cQ
    @3
    cU
    cE
    cF
    cH
    c.or
    cK
    c.le
    c.an
    @1
    cF
    @3
    @0
    c.or
    co
    cW
    c.an
    co
    c.or
    co
    c.an
    co
    #
    cV
    cW
    vs
    cdleme26.b
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme27.u
    cdleme27.f
    @61
    eqid
    #
    vs
    vu
    cA
    cB
    cP
    cQ
    @3
    cU
    @10
    @58
    wa
    @54
    @61
    wceq
    wi
    vs
    cA
    wral
    vu
    cB
    crio
    #
    cZ
    cF
    cE
    c.or
    c.le
    c.an
    cO
    @61
    cW
    vz
    cdleme27.z
    cdleme27.o
    cdleme27.f
    @62
    cdleme27.e
    @63
    eqid
    cdleme25cv
    cdleme26f2
    syl333anc
    @58
    cC
    cF
    wceq
    #
    @4
    @31
    @58
    cC
    @44
    cF
    cdleme27.c
    @2
    cD
    cF
    iffalse
    syl5eq
    #
    ad2antrr
    @4
    @46
    @58
    @31
    @48
    ad2antlr
    3brtr4d
    ex
    @58
    @42
    wa
    #
    @31
    @33
    @66
    @31
    wa
    #
    cF
    @51
    cC
    @32
    c.le
    @67
    @7
    @21
    @42
    @58
    @8
    w3a
    @15
    @18
    @11
    @26
    @29
    cF
    @51
    c.le
    wbr
    @7
    @8
    @11
    @22
    @30
    @66
    simpr11
    @15
    @18
    @21
    @12
    @30
    @66
    simpr23
    @67
    @42
    @58
    @8
    @58
    @42
    @31
    simplr
    @58
    @42
    @31
    simpll
    @7
    @8
    @11
    @22
    @30
    @66
    simpr12
    3jca
    @15
    @18
    @21
    @12
    @30
    @66
    simpr21
    @15
    @18
    @21
    @12
    @30
    @66
    simpr22
    @7
    @8
    @11
    @22
    @30
    @66
    simpr13
    @26
    @29
    @12
    @22
    @66
    simpr3l
    @26
    @29
    @12
    @22
    @66
    simpr3r
    cA
    cP
    cQ
    @0
    @3
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme27.u
    cdleme27.f
    cdleme27.g
    cdleme22g
    syl323anc
    @58
    @64
    @42
    @31
    @65
    ad2antrr
    @42
    @56
    @58
    @31
    @57
    ad2antlr
    3brtr4d
    ex
    4cases
end
