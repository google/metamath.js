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
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21l.mm"
include "simp22l.mm"
include "jca.mm"
include "simp23.mm"
include "simp311.mm"
include "simp32l.mm"
include "simp33.mm"
include "cdleme22e.mm"
include "syl133anc.mm"
include "simp21r.mm"
include "simp312.mm"
include "cdleme25cl.mm"
include "syl322anc.mm"
include "simp33l.mm"
include "simp33r.mm"
include "simp32r.mm"
include "cbs.mm"
include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "riotasv.mm"
include "syl3anc.mm"
include "simp22r.mm"
include "simp313.mm"
include "oveq1d.mm"
include "3brtr4d.mm"

theorem cdleme26e
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
  assume cdleme26e.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme26e.f: |- F = ( ( z .\/ U ) ./\ ( Q .\/ ( ( P .\/ z ) ./\ W ) ) )
  assume cdleme26e.n: |- N = ( ( P .\/ Q ) ./\ ( F .\/ ( ( S .\/ z ) ./\ W ) ) )
  assume cdleme26e.o: |- O = ( ( P .\/ Q ) ./\ ( F .\/ ( ( T .\/ z ) ./\ W ) ) )
  assume cdleme26e.i: |- I = ( iota_ u e. B A. z e. A ( ( -. z .<_ W /\ -. z .<_ ( P .\/ Q ) ) -> u = N ) )
  assume cdleme26e.e: |- E = ( iota_ u e. B A. z e. A ( ( -. z .<_ W /\ -. z .<_ ( P .\/ Q ) ) -> u = O ) )

  disjoint u z
  disjoint A z
  disjoint A u
  disjoint B z
  disjoint B u
  disjoint H z
  disjoint .\/ z
  disjoint .\/ u
  disjoint K z
  disjoint .<_ z
  disjoint .<_ u
  disjoint ./\ z
  disjoint ./\ u
  disjoint N u
  disjoint O u
  disjoint P z
  disjoint P u
  disjoint Q z
  disjoint Q u
  disjoint S z
  disjoint S u
  disjoint T z
  disjoint T u
  disjoint U z
  disjoint U u
  disjoint W z
  disjoint W u
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( V e. A /\ V .<_ W ) ) /\ ( ( P =/= Q /\ S .<_ ( P .\/ Q ) /\ T .<_ ( P .\/ Q ) ) /\ ( ( T .\/ V ) = ( P .\/ Q ) /\ -. z .<_ ( P .\/ Q ) ) /\ ( z e. A /\ -. z .<_ W ) ) ) -> I .<_ ( E .\/ V ) )

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
    wa
    #
    cV
    cA
    wcel
    cV
    cW
    c.le
    wbr
    wa
    #
    w3a
    #
    cP
    cQ
    wne
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
    cT
    @13
    c.le
    wbr
    #
    w3a
    #
    cT
    cV
    c.or
    co
    @13
    wceq
    #
    vz
    cv
    #
    @13
    c.le
    wbr
    wn
    #
    wa
    #
    @18
    cA
    wcel
    #
    @18
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
    @25
    @0
    @1
    @2
    @4
    @7
    wa
    @10
    @12
    @17
    wa
    @23
    cN
    @26
    c.le
    wbr
    @0
    @1
    @2
    @11
    @24
    simp11
    #
    @0
    @1
    @2
    @11
    @24
    simp12
    #
    @0
    @1
    @2
    @11
    @24
    simp13
    #
    @25
    @4
    @7
    @4
    @5
    @9
    @10
    @3
    @24
    simp21l
    #
    @7
    @8
    @6
    @10
    @3
    @24
    simp22l
    #
    jca
    @3
    @6
    @9
    @10
    @24
    simp23
    @25
    @12
    @17
    @12
    @14
    @15
    @20
    @23
    @3
    @11
    simp311
    #
    @17
    @19
    @16
    @23
    @3
    @11
    simp32l
    jca
    @3
    @11
    @16
    @20
    @23
    simp33
    vz
    cA
    cP
    cQ
    cS
    cT
    cU
    cF
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
    cdleme26e.u
    cdleme26e.f
    cdleme26e.n
    cdleme26e.o
    cdleme22e
    syl133anc
    @25
    cI
    cB
    wcel
    #
    @21
    @22
    @19
    wa
    #
    cI
    cN
    wceq
    @25
    @0
    @1
    @2
    @4
    @5
    @12
    @14
    @33
    @27
    @28
    @29
    @30
    @4
    @5
    @9
    @10
    @3
    @24
    simp21r
    @32
    @12
    @14
    @15
    @20
    @23
    @3
    @11
    simp312
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
    vz
    cdleme26.b
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme26e.u
    cdleme26e.f
    cdleme26e.n
    cdleme26e.i
    cdleme25cl
    syl322anc
    @21
    @22
    @16
    @20
    @3
    @11
    simp33l
    #
    @25
    @22
    @19
    @21
    @22
    @16
    @20
    @3
    @11
    simp33r
    @17
    @19
    @16
    @23
    @3
    @11
    simp32r
    jca
    #
    @34
    vu
    vz
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
    cdleme26e.i
    riotasv
    syl3anc
    @25
    cE
    cO
    cV
    c.or
    @25
    cE
    cB
    wcel
    #
    @21
    @34
    cE
    cO
    wceq
    @25
    @0
    @1
    @2
    @7
    @8
    @12
    @15
    @38
    @27
    @28
    @29
    @31
    @7
    @8
    @6
    @10
    @3
    @24
    simp22r
    @32
    @12
    @14
    @15
    @20
    @23
    @3
    @11
    simp313
    vu
    cA
    cB
    cP
    cQ
    cT
    cU
    cF
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
    cdleme26e.u
    cdleme26e.f
    cdleme26e.o
    cdleme26e.e
    cdleme25cl
    syl322anc
    @35
    @36
    @34
    vu
    vz
    cB
    cA
    cO
    cE
    @37
    cdleme26e.e
    riotasv
    syl3anc
    oveq1d
    3brtr4d
end
