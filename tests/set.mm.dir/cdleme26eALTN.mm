include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "simp11l.mm"
include "simp11r.mm"
include "simp231.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21.mm"
include "simp221.mm"
include "simp31.mm"
include "3ad2ant3.mm"
include "simp322.mm"
include "simp332.mm"
include "jca.mm"
include "jca31.mm"
include "cdleme22eALTN.mm"
include "syl333anc.mm"
include "simp11.mm"
include "simp222.mm"
include "simp223.mm"
include "cdleme25cl.mm"
include "syl322anc.mm"
include "simp323.mm"
include "cbs.mm"
include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "riotasv.mm"
include "syl112anc.mm"
include "simp232.mm"
include "simp233.mm"
include "simp333.mm"
include "oveq1d.mm"
include "3brtr4d.mm"

theorem cdleme26eALTN
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
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
  assume cdleme26.b: |- B = ( Base ` K )
  assume cdleme26.l: |- .<_ = ( le ` K )
  assume cdleme26.j: |- .\/ = ( join ` K )
  assume cdleme26.m: |- ./\ = ( meet ` K )
  assume cdleme26.a: |- A = ( Atoms ` K )
  assume cdleme26.h: |- H = ( LHyp ` K )
  assume cdleme26eALT.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme26eALT.f: |- F = ( ( y .\/ U ) ./\ ( Q .\/ ( ( P .\/ y ) ./\ W ) ) )
  assume cdleme26eALT.g: |- G = ( ( z .\/ U ) ./\ ( Q .\/ ( ( P .\/ z ) ./\ W ) ) )
  assume cdleme26eALT.n: |- N = ( ( P .\/ Q ) ./\ ( F .\/ ( ( S .\/ y ) ./\ W ) ) )
  assume cdleme26eALT.o: |- O = ( ( P .\/ Q ) ./\ ( G .\/ ( ( T .\/ z ) ./\ W ) ) )
  assume cdleme26eALT.i: |- I = ( iota_ u e. B A. y e. A ( ( -. y .<_ W /\ -. y .<_ ( P .\/ Q ) ) -> u = N ) )
  assume cdleme26eALT.e: |- E = ( iota_ u e. B A. z e. A ( ( -. z .<_ W /\ -. z .<_ ( P .\/ Q ) ) -> u = O ) )

  disjoint y z
  disjoint u y
  disjoint A y
  disjoint u z
  disjoint A z
  disjoint A u
  disjoint B y
  disjoint B z
  disjoint B u
  disjoint H y
  disjoint H z
  disjoint .\/ y
  disjoint .\/ z
  disjoint .\/ u
  disjoint K y
  disjoint K z
  disjoint .<_ y
  disjoint .<_ z
  disjoint .<_ u
  disjoint ./\ y
  disjoint ./\ z
  disjoint ./\ u
  disjoint N u
  disjoint O u
  disjoint P y
  disjoint P z
  disjoint P u
  disjoint Q y
  disjoint Q z
  disjoint Q u
  disjoint S y
  disjoint S u
  disjoint T z
  disjoint T u
  disjoint U y
  disjoint U z
  disjoint U u
  disjoint W y
  disjoint W z
  disjoint W u
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( S e. A /\ -. S .<_ W /\ S .<_ ( P .\/ Q ) ) /\ ( T e. A /\ -. T .<_ W /\ T .<_ ( P .\/ Q ) ) ) /\ ( ( V e. A /\ V .<_ W /\ ( T .\/ V ) = ( P .\/ Q ) ) /\ ( y e. A /\ -. y .<_ W /\ -. y .<_ ( P .\/ Q ) ) /\ ( z e. A /\ -. z .<_ W /\ -. z .<_ ( P .\/ Q ) ) ) ) -> I .<_ ( E .\/ V ) )

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
    cS
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    cT
    cA
    wcel
    #
    cT
    cW
    c.le
    wbr
    wn
    #
    cT
    @9
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    cV
    cA
    wcel
    cV
    cW
    c.le
    wbr
    cT
    cV
    c.or
    co
    @9
    wceq
    w3a
    #
    vy
    cv
    #
    cA
    wcel
    #
    @18
    cW
    c.le
    wbr
    wn
    #
    @18
    @9
    c.le
    wbr
    wn
    #
    w3a
    #
    vz
    cv
    #
    cA
    wcel
    #
    @23
    cW
    c.le
    wbr
    wn
    #
    @23
    @9
    c.le
    wbr
    wn
    #
    w3a
    #
    w3a
    #
    w3a
    #
    cN
    cO
    cV
    c.or
    co
    #
    cI
    cE
    cV
    c.or
    co
    c.le
    @29
    @0
    @1
    @12
    @3
    @4
    @6
    @7
    @17
    @19
    @20
    wa
    @24
    @25
    wa
    #
    wa
    cN
    @30
    c.le
    wbr
    @0
    @1
    @3
    @4
    @16
    @28
    simp11l
    @0
    @1
    @3
    @4
    @16
    @28
    simp11r
    @12
    @13
    @14
    @6
    @11
    @5
    @28
    simp231
    #
    @2
    @3
    @4
    @16
    @28
    simp12
    #
    @2
    @3
    @4
    @16
    @28
    simp13
    #
    @5
    @6
    @11
    @15
    @28
    simp21
    #
    @7
    @8
    @10
    @6
    @15
    @5
    @28
    simp221
    #
    @5
    @16
    @17
    @22
    @27
    simp31
    @29
    @19
    @20
    @31
    @28
    @5
    @19
    @16
    @17
    @19
    @20
    @21
    @27
    simp21
    3ad2ant3
    #
    @19
    @20
    @21
    @17
    @27
    @5
    @16
    simp322
    #
    @29
    @24
    @25
    @28
    @5
    @24
    @16
    @17
    @22
    @24
    @25
    @26
    simp31
    3ad2ant3
    #
    @24
    @25
    @26
    @17
    @22
    @5
    @16
    simp332
    #
    jca
    jca31
    vy
    vz
    cA
    cP
    cQ
    cS
    cT
    cU
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
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme26eALT.u
    cdleme26eALT.f
    cdleme26eALT.g
    cdleme26eALT.n
    cdleme26eALT.o
    cdleme22eALTN
    syl333anc
    @29
    cI
    cB
    wcel
    #
    @19
    @20
    @21
    cI
    cN
    wceq
    @29
    @2
    @3
    @4
    @7
    @8
    @6
    @10
    @41
    @2
    @3
    @4
    @16
    @28
    simp11
    #
    @33
    @34
    @36
    @7
    @8
    @10
    @6
    @15
    @5
    @28
    simp222
    @35
    @7
    @8
    @10
    @6
    @15
    @5
    @28
    simp223
    vu
    cA
    cB
    cP
    cQ
    cS
    cU
    cF
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    cW
    vy
    cdleme26.b
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme26eALT.u
    cdleme26eALT.f
    cdleme26eALT.n
    cdleme26eALT.i
    cdleme25cl
    syl322anc
    @37
    @38
    @19
    @20
    @21
    @17
    @27
    @5
    @16
    simp323
    @20
    @21
    wa
    vu
    vy
    cB
    cA
    cN
    cI
    cB
    cK
    cbs
    cfv
    cvv
    cdleme26.b
    cK
    cbs
    fvex
    eqeltri
    #
    cdleme26eALT.i
    riotasv
    syl112anc
    @29
    cE
    cO
    cV
    c.or
    @29
    cE
    cB
    wcel
    #
    @24
    @25
    @26
    cE
    cO
    wceq
    @29
    @2
    @3
    @4
    @12
    @13
    @6
    @14
    @44
    @42
    @33
    @34
    @32
    @12
    @13
    @14
    @6
    @11
    @5
    @28
    simp232
    @35
    @12
    @13
    @14
    @6
    @11
    @5
    @28
    simp233
    vu
    cA
    cB
    cP
    cQ
    cT
    cU
    cG
    cH
    cE
    c.or
    cK
    c.le
    c.an
    cO
    cW
    vz
    cdleme26.b
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme26eALT.u
    cdleme26eALT.g
    cdleme26eALT.o
    cdleme26eALT.e
    cdleme25cl
    syl322anc
    @39
    @40
    @24
    @25
    @26
    @17
    @22
    @5
    @16
    simp333
    @25
    @26
    wa
    vu
    vz
    cB
    cA
    cO
    cE
    @43
    cdleme26eALT.e
    riotasv
    syl112anc
    oveq1d
    3brtr4d
end
