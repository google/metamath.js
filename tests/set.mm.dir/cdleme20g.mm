include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "simp11l.mm"
include "simp11r.mm"
include "simp21l.mm"
include "simp21r.mm"
include "simp23l.mm"
include "simp33.mm"
include "simp32l.mm"
include "cdlemeda.mm"
include "syl223anc.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "cdleme10.mm"
include "syl212anc.mm"
include "eqtrd.mm"
include "simp22l.mm"
include "simp22r.mm"
include "simp32r.mm"
include "oveq12d.mm"
include "simp12l.mm"
include "simp13l.mm"
include "simp21.mm"
include "cdleme1.mm"
include "syl23anc.mm"
include "simp22.mm"

theorem cdleme20g
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  let cY: class Y
  assume cdleme19.l: |- .<_ = ( le ` K )
  assume cdleme19.j: |- .\/ = ( join ` K )
  assume cdleme19.m: |- ./\ = ( meet ` K )
  assume cdleme19.a: |- A = ( Atoms ` K )
  assume cdleme19.h: |- H = ( LHyp ` K )
  assume cdleme19.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme19.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme19.g: |- G = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )
  assume cdleme19.d: |- D = ( ( R .\/ S ) ./\ W )
  assume cdleme19.y: |- Y = ( ( R .\/ T ) ./\ W )
  assume cdleme20.v: |- V = ( ( S .\/ T ) ./\ W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) /\ ( ( P =/= Q /\ S =/= T ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) ) /\ R .<_ ( P .\/ Q ) ) ) -> ( ( ( D .\/ S ) ./\ ( Y .\/ T ) ) .\/ ( ( S .\/ F ) ./\ ( T .\/ G ) ) ) = ( ( ( S .\/ R ) ./\ ( T .\/ R ) ) .\/ ( ( S .\/ U ) ./\ ( T .\/ U ) ) ) )

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
    #
    cT
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cR
    cA
    wcel
    #
    cR
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
    cQ
    wne
    cS
    cT
    wne
    wa
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
    @21
    c.le
    wbr
    wn
    #
    wa
    #
    cR
    @21
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    cD
    cS
    c.or
    co
    #
    cY
    cT
    c.or
    co
    #
    c.an
    co
    cS
    cR
    c.or
    co
    #
    cT
    cR
    c.or
    co
    #
    c.an
    co
    cS
    cF
    c.or
    co
    #
    cT
    cG
    c.or
    co
    #
    c.an
    co
    cS
    cU
    c.or
    co
    #
    cT
    cU
    c.or
    co
    #
    c.an
    co
    c.or
    @27
    @28
    @30
    @29
    @31
    c.an
    @27
    @28
    cS
    cD
    c.or
    co
    #
    @30
    @27
    @0
    cD
    cA
    wcel
    #
    @10
    @28
    @36
    wceq
    @0
    @1
    @5
    @8
    @19
    @26
    simp11l
    #
    @27
    @0
    @1
    @10
    @11
    @16
    @25
    @22
    @37
    @38
    @0
    @1
    @5
    @8
    @19
    @26
    simp11r
    #
    @10
    @11
    @15
    @18
    @9
    @26
    simp21l
    #
    @10
    @11
    @15
    @18
    @9
    @26
    simp21r
    #
    @16
    @17
    @12
    @15
    @9
    @26
    simp23l
    #
    @9
    @19
    @20
    @24
    @25
    simp33
    #
    @22
    @23
    @20
    @25
    @9
    @19
    simp32l
    cA
    cD
    cP
    cQ
    cR
    cS
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.d
    cdlemeda
    syl223anc
    @40
    cA
    c.or
    cK
    cD
    cS
    cdleme19.j
    cdleme19.a
    hlatjcom
    syl3anc
    @27
    @0
    @1
    @16
    @10
    @11
    @36
    @30
    wceq
    @38
    @39
    @42
    @40
    @41
    cA
    cD
    cR
    cS
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.d
    cdleme10
    syl212anc
    eqtrd
    @27
    @29
    cT
    cY
    c.or
    co
    #
    @31
    @27
    @0
    cY
    cA
    wcel
    #
    @13
    @29
    @44
    wceq
    @38
    @27
    @0
    @1
    @13
    @14
    @16
    @25
    @23
    @45
    @38
    @39
    @13
    @14
    @12
    @18
    @9
    @26
    simp22l
    #
    @13
    @14
    @12
    @18
    @9
    @26
    simp22r
    #
    @42
    @43
    @22
    @23
    @20
    @25
    @9
    @19
    simp32r
    cA
    cY
    cP
    cQ
    cR
    cT
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.y
    cdlemeda
    syl223anc
    @46
    cA
    c.or
    cK
    cY
    cT
    cdleme19.j
    cdleme19.a
    hlatjcom
    syl3anc
    @27
    @0
    @1
    @16
    @13
    @14
    @44
    @31
    wceq
    @38
    @39
    @42
    @46
    @47
    cA
    cY
    cR
    cT
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.y
    cdleme10
    syl212anc
    eqtrd
    oveq12d
    @27
    @32
    @34
    @33
    @35
    c.an
    @27
    @0
    @1
    @3
    @6
    @12
    @32
    @34
    wceq
    @38
    @39
    @3
    @4
    @2
    @8
    @19
    @26
    simp12l
    #
    @6
    @7
    @2
    @5
    @19
    @26
    simp13l
    #
    @9
    @12
    @15
    @18
    @26
    simp21
    cA
    cP
    cQ
    cS
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.u
    cdleme19.f
    cdleme1
    syl23anc
    @27
    @0
    @1
    @3
    @6
    @15
    @33
    @35
    wceq
    @38
    @39
    @48
    @49
    @9
    @12
    @15
    @18
    @26
    simp22
    cA
    cP
    cQ
    cT
    cU
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.u
    cdleme19.g
    cdleme1
    syl23anc
    oveq12d
    oveq12d
end
