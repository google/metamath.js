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
include "simp2l.mm"
include "simp2r.mm"
include "simp33l.mm"
include "simp31.mm"
include "simp11l.mm"
include "simp12l.mm"
include "simp13l.mm"
include "simp2rl.mm"
include "simp32l.mm"
include "simpld.mm"
include "simp33r.mm"
include "cdleme21a.mm"
include "syl322anc.mm"
include "jca.mm"
include "cdleme21b.mm"
include "syl332anc.mm"
include "simp32r.mm"
include "3jca.mm"
include "cdleme21c.mm"
include "eqid.mm"
include "cdleme20.mm"
include "syl333anc.mm"

theorem cdleme21d
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( P =/= Q /\ ( -. S .<_ ( P .\/ Q ) /\ R .<_ ( P .\/ Q ) ) /\ ( ( z e. A /\ -. z .<_ W ) /\ ( P .\/ z ) = ( S .\/ z ) ) ) ) -> N = Z )

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
    cR
    @16
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
    @20
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cP
    @20
    c.or
    co
    cS
    @20
    c.or
    co
    #
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
    @10
    @13
    @23
    @15
    cS
    @20
    wne
    #
    wa
    @17
    @20
    @16
    c.le
    wbr
    wn
    #
    @18
    w3a
    cU
    @24
    c.le
    wbr
    wn
    #
    cN
    cZ
    wceq
    @2
    @5
    @8
    @14
    @27
    simp11
    #
    @2
    @5
    @8
    @14
    @27
    simp12
    #
    @2
    @5
    @8
    @14
    @27
    simp13
    @9
    @10
    @13
    @27
    simp2l
    @9
    @10
    @13
    @27
    simp2r
    @23
    @25
    @15
    @19
    @9
    @14
    simp33l
    #
    @28
    @15
    @29
    @9
    @14
    @15
    @19
    @26
    simp31
    #
    @28
    @0
    @3
    @6
    @11
    @17
    @21
    @25
    @29
    @0
    @1
    @5
    @8
    @14
    @27
    simp11l
    #
    @3
    @4
    @2
    @8
    @14
    @27
    simp12l
    #
    @6
    @7
    @2
    @5
    @14
    @27
    simp13l
    #
    @11
    @12
    @10
    @9
    @27
    simp2rl
    #
    @17
    @18
    @15
    @26
    @9
    @14
    simp32l
    #
    @28
    @21
    @22
    @34
    simpld
    #
    @23
    @25
    @15
    @19
    @9
    @14
    simp33r
    #
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
    cdleme21a
    syl322anc
    jca
    @28
    @17
    @30
    @18
    @40
    @28
    @0
    @3
    @6
    @11
    @15
    @17
    @21
    @25
    @30
    @36
    @37
    @38
    @39
    @35
    @40
    @41
    @42
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
    @17
    @18
    @15
    @26
    @9
    @14
    simp32r
    3jca
    @28
    @2
    @5
    @6
    @11
    @15
    @17
    @21
    @25
    @31
    @32
    @33
    @38
    @39
    @35
    @40
    @41
    @42
    vz
    cA
    cP
    cQ
    cS
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
    cdleme21c
    syl332anc
    cA
    cD
    cP
    cQ
    cR
    cS
    @20
    cU
    cF
    cB
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cZ
    @24
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
    cdleme21.f
    cdleme21.b
    cdleme21.d
    cdleme21.e
    @43
    eqid
    cdleme21d.n
    cdleme21d.z
    cdleme20
    syl333anc
end
