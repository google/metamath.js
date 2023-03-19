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
include "simp23.mm"
include "simp21l.mm"
include "simp22l.mm"
include "simp33l.mm"
include "simp32l.mm"
include "simp33r.mm"
include "cdleme19a.mm"
include "syl133anc.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21.mm"
include "simp22.mm"
include "simp31.mm"
include "simp32r.mm"
include "cdleme16.mm"
include "syl332anc.mm"
include "eqtrd.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "hllat.mm"
include "syl.mm"
include "simp11r.mm"
include "simp12l.mm"
include "simp13l.mm"
include "eqid.mm"
include "cdleme1b.mm"
include "syl23anc.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "lhpbase.mm"
include "latmle1.mm"
include "eqbrtrd.mm"

theorem cdleme19b
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ R e. A ) /\ ( ( P =/= Q /\ S =/= T ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) ) /\ ( R .<_ ( P .\/ Q ) /\ R .<_ ( S .\/ T ) ) ) ) -> D .<_ ( F .\/ G ) )

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
    @19
    c.le
    wbr
    wn
    #
    wa
    #
    cR
    @19
    c.le
    wbr
    #
    cR
    cS
    cT
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    w3a
    #
    cD
    cF
    cG
    c.or
    co
    #
    cW
    c.an
    co
    #
    @29
    c.le
    @28
    cD
    @24
    cW
    c.an
    co
    #
    @30
    @28
    @0
    @16
    @10
    @13
    @23
    @20
    @25
    cD
    @31
    wceq
    @0
    @1
    @5
    @8
    @17
    @27
    simp11l
    #
    @9
    @12
    @15
    @16
    @27
    simp23
    @10
    @11
    @15
    @16
    @9
    @27
    simp21l
    #
    @13
    @14
    @12
    @16
    @9
    @27
    simp22l
    #
    @23
    @25
    @18
    @22
    @9
    @17
    simp33l
    @20
    @21
    @18
    @26
    @9
    @17
    simp32l
    #
    @23
    @25
    @18
    @22
    @9
    @17
    simp33r
    cA
    cD
    cP
    cQ
    cR
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
    cW
    cY
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.u
    cdleme19.f
    cdleme19.g
    cdleme19.d
    cdleme19.y
    cdleme19a
    syl133anc
    @28
    @2
    @5
    @8
    @12
    @15
    @18
    @20
    @21
    @31
    @30
    wceq
    @2
    @5
    @8
    @17
    @27
    simp11
    @2
    @5
    @8
    @17
    @27
    simp12
    @2
    @5
    @8
    @17
    @27
    simp13
    @9
    @12
    @15
    @16
    @27
    simp21
    @9
    @12
    @15
    @16
    @27
    simp22
    @9
    @17
    @18
    @22
    @26
    simp31
    @35
    @20
    @21
    @18
    @26
    @9
    @17
    simp32r
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
    cW
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.u
    cdleme19.f
    cdleme19.g
    cdleme16
    syl332anc
    eqtrd
    @28
    cK
    clat
    wcel
    #
    @29
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @37
    wcel
    #
    @30
    @29
    c.le
    wbr
    @28
    @0
    @36
    @32
    cK
    hllat
    syl
    #
    @28
    @36
    cF
    @37
    wcel
    #
    cG
    @37
    wcel
    #
    @38
    @40
    @28
    @0
    @1
    @3
    @6
    @10
    @41
    @32
    @0
    @1
    @5
    @8
    @17
    @27
    simp11r
    #
    @3
    @4
    @2
    @8
    @17
    @27
    simp12l
    #
    @6
    @7
    @2
    @5
    @17
    @27
    simp13l
    #
    @33
    cA
    @37
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
    @37
    eqid
    #
    cdleme1b
    syl23anc
    @28
    @0
    @1
    @3
    @6
    @13
    @42
    @32
    @43
    @44
    @45
    @34
    cA
    @37
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
    @46
    cdleme1b
    syl23anc
    @37
    c.or
    cK
    cF
    cG
    @46
    cdleme19.j
    latjcl
    syl3anc
    @28
    @1
    @39
    @43
    @37
    cH
    cK
    cW
    @46
    cdleme19.h
    lhpbase
    syl
    @37
    cK
    c.le
    c.an
    @29
    cW
    @46
    cdleme19.l
    cdleme19.m
    latmle1
    syl3anc
    eqbrtrd
end
