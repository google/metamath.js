include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp31.mm"
include "simp22.mm"
include "simp33l.mm"
include "simp231.mm"
include "simp13l.mm"
include "simp21l.mm"
include "simp232.mm"
include "3jca.mm"
include "simp32r.mm"
include "simpld.mm"
include "simp33r.mm"
include "cdleme21at.mm"
include "syl322anc.mm"
include "jca.mm"
include "simp233.mm"
include "simp11l.mm"
include "simp12l.mm"
include "cdleme21b.mm"
include "syl332anc.mm"
include "simp32l.mm"
include "simp21.mm"
include "cdleme21ct.mm"
include "eqid.mm"
include "cdleme20.mm"
include "syl333anc.mm"

theorem cdleme21e
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
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
  let cY: class Y
  let cZ: class Z
  assume cdleme21.l: |- .<_ = ( le ` K )
  assume cdleme21.j: |- .\/ = ( join ` K )
  assume cdleme21.m: |- ./\ = ( meet ` K )
  assume cdleme21.a: |- A = ( Atoms ` K )
  assume cdleme21.h: |- H = ( LHyp ` K )
  assume cdleme21.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme21.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme21.b: |- B = ( ( z .\/ U ) ./\ ( Q .\/ ( ( P .\/ z ) ./\ W ) ) )
  assume cdleme21.d: |- D = ( ( R .\/ S ) ./\ W )
  assume cdleme21.e: |- E = ( ( R .\/ z ) ./\ W )
  assume cdleme21d.n: |- N = ( ( P .\/ Q ) ./\ ( F .\/ D ) )
  assume cdleme21d.z: |- Z = ( ( P .\/ Q ) ./\ ( B .\/ E ) )
  assume cdleme21.g: |- G = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )
  assume cdleme21.y: |- Y = ( ( R .\/ T ) ./\ W )
  assume cdleme21.o: |- O = ( ( P .\/ Q ) ./\ ( G .\/ Y ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( P =/= Q /\ -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( R .<_ ( P .\/ Q ) /\ U .<_ ( S .\/ T ) ) /\ ( ( z e. A /\ -. z .<_ W ) /\ ( P .\/ z ) = ( S .\/ z ) ) ) ) -> O = Z )

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
    cT
    cW
    c.le
    wbr
    wn
    wa
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
    wn
    #
    cT
    @15
    c.le
    wbr
    wn
    #
    w3a
    #
    w3a
    #
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    #
    cR
    @15
    c.le
    wbr
    #
    cU
    cS
    cT
    c.or
    co
    c.le
    wbr
    #
    wa
    #
    vz
    cv
    #
    cA
    wcel
    #
    @24
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cP
    @24
    c.or
    co
    cS
    @24
    c.or
    co
    wceq
    #
    wa
    #
    w3a
    #
    w3a
    #
    @2
    @5
    @8
    @20
    @13
    @27
    @14
    cT
    @24
    wne
    #
    wa
    @17
    @24
    @15
    c.le
    wbr
    wn
    #
    @21
    w3a
    cU
    cT
    @24
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cO
    cZ
    wceq
    @2
    @5
    @8
    @19
    @30
    simp11
    #
    @2
    @5
    @8
    @19
    @30
    simp12
    #
    @2
    @5
    @8
    @19
    @30
    simp13
    @9
    @19
    @20
    @23
    @29
    simp31
    @9
    @12
    @13
    @18
    @30
    simp22
    #
    @27
    @28
    @20
    @23
    @9
    @19
    simp33l
    #
    @31
    @14
    @32
    @14
    @16
    @17
    @12
    @13
    @9
    @30
    simp231
    #
    @31
    @2
    @5
    @6
    @10
    @14
    @16
    w3a
    @22
    @25
    @28
    @32
    @36
    @37
    @6
    @7
    @2
    @5
    @19
    @30
    simp13l
    #
    @31
    @10
    @14
    @16
    @10
    @11
    @13
    @18
    @9
    @30
    simp21l
    #
    @40
    @14
    @16
    @17
    @12
    @13
    @9
    @30
    simp232
    #
    3jca
    @21
    @22
    @20
    @29
    @9
    @19
    simp32r
    #
    @31
    @25
    @26
    @39
    simpld
    #
    @27
    @28
    @20
    @23
    @9
    @19
    simp33r
    #
    vz
    cA
    cP
    cQ
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme21.l
    cdleme21.j
    cdleme21.m
    cdleme21.a
    cdleme21.h
    cdleme21.u
    cdleme21at
    syl322anc
    jca
    @31
    @17
    @33
    @21
    @14
    @16
    @17
    @12
    @13
    @9
    @30
    simp233
    @31
    @0
    @3
    @6
    @10
    @14
    @16
    @25
    @28
    @33
    @0
    @1
    @5
    @8
    @19
    @30
    simp11l
    @3
    @4
    @2
    @8
    @19
    @30
    simp12l
    @41
    @42
    @40
    @43
    @45
    @46
    vz
    cA
    cP
    cQ
    cS
    c.or
    cK
    c.le
    cdleme21.l
    cdleme21.j
    cdleme21.a
    cdleme21b
    syl332anc
    @21
    @22
    @20
    @29
    @9
    @19
    simp32l
    3jca
    @31
    @2
    @5
    @6
    @12
    @13
    @14
    @16
    @22
    w3a
    @27
    @28
    @35
    @36
    @37
    @41
    @9
    @12
    @13
    @18
    @30
    simp21
    @38
    @31
    @14
    @16
    @22
    @40
    @43
    @44
    3jca
    @39
    @46
    vz
    cA
    cP
    cQ
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme21.l
    cdleme21.j
    cdleme21.m
    cdleme21.a
    cdleme21.h
    cdleme21.u
    cdleme21ct
    syl332anc
    cA
    cY
    cP
    cQ
    cR
    cT
    @24
    cU
    cG
    cB
    cH
    c.or
    cK
    c.le
    c.an
    cO
    cZ
    @34
    cW
    c.an
    co
    #
    cW
    cE
    cdleme21.l
    cdleme21.j
    cdleme21.m
    cdleme21.a
    cdleme21.h
    cdleme21.u
    cdleme21.g
    cdleme21.b
    cdleme21.y
    cdleme21.e
    @47
    eqid
    cdleme21.o
    cdleme21d.z
    cdleme20
    syl333anc
end
