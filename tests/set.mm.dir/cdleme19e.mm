include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp11r.mm"
include "simp12l.mm"
include "simp13l.mm"
include "simp21l.mm"
include "eqid.mm"
include "cdleme1b.mm"
include "syl23anc.mm"
include "simp22l.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "cdleme19d.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp22.mm"
include "simp21.mm"
include "simp23.mm"
include "simp31l.mm"
include "simp31r.mm"
include "necomd.mm"
include "jca.mm"
include "simp32r.mm"
include "simp32l.mm"
include "simp33l.mm"
include "simp33r.mm"
include "hlatjcom.mm"
include "breqtrd.mm"
include "syl333anc.mm"
include "3eqtr4d.mm"

theorem cdleme19e
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ R e. A ) /\ ( ( P =/= Q /\ S =/= T ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) ) /\ ( R .<_ ( P .\/ Q ) /\ R .<_ ( S .\/ T ) ) ) ) -> ( F .\/ D ) = ( G .\/ Y ) )

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
    #
    cS
    cT
    wne
    #
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
    cF
    cG
    c.or
    co
    #
    cG
    cF
    c.or
    co
    #
    cF
    cD
    c.or
    co
    cG
    cY
    c.or
    co
    #
    @30
    cK
    clat
    wcel
    #
    cF
    cK
    cbs
    cfv
    #
    wcel
    #
    cG
    @35
    wcel
    #
    @31
    @32
    wceq
    @30
    @0
    @34
    @0
    @1
    @5
    @8
    @17
    @29
    simp11l
    #
    cK
    hllat
    syl
    @30
    @0
    @1
    @3
    @6
    @10
    @36
    @38
    @0
    @1
    @5
    @8
    @17
    @29
    simp11r
    #
    @3
    @4
    @2
    @8
    @17
    @29
    simp12l
    #
    @6
    @7
    @2
    @5
    @17
    @29
    simp13l
    #
    @10
    @11
    @15
    @16
    @9
    @29
    simp21l
    #
    cA
    @35
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
    @35
    eqid
    #
    cdleme1b
    syl23anc
    @30
    @0
    @1
    @3
    @6
    @13
    @37
    @38
    @39
    @40
    @41
    @13
    @14
    @12
    @16
    @9
    @29
    simp22l
    #
    cA
    @35
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
    @43
    cdleme1b
    syl23anc
    @35
    c.or
    cK
    cF
    cG
    @43
    cdleme19.j
    latjcom
    syl3anc
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
    cdleme19d
    @30
    @2
    @5
    @8
    @15
    @12
    @16
    @18
    cT
    cS
    wne
    #
    wa
    @23
    @22
    wa
    @25
    cR
    cT
    cS
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    @33
    @32
    wceq
    @2
    @5
    @8
    @17
    @29
    simp11
    @2
    @5
    @8
    @17
    @29
    simp12
    @2
    @5
    @8
    @17
    @29
    simp13
    @9
    @12
    @15
    @16
    @29
    simp22
    @9
    @12
    @15
    @16
    @29
    simp21
    @9
    @12
    @15
    @16
    @29
    simp23
    @30
    @18
    @45
    @18
    @19
    @24
    @28
    @9
    @17
    simp31l
    @30
    cS
    cT
    @18
    @19
    @24
    @28
    @9
    @17
    simp31r
    necomd
    jca
    @30
    @23
    @22
    @22
    @23
    @20
    @28
    @9
    @17
    simp32r
    @22
    @23
    @20
    @28
    @9
    @17
    simp32l
    jca
    @30
    @25
    @47
    @25
    @27
    @20
    @24
    @9
    @17
    simp33l
    @30
    cR
    @26
    @46
    c.le
    @25
    @27
    @20
    @24
    @9
    @17
    simp33r
    @30
    @0
    @10
    @13
    @26
    @46
    wceq
    @38
    @42
    @44
    cA
    c.or
    cK
    cS
    cT
    cdleme19.j
    cdleme19.a
    hlatjcom
    syl3anc
    breqtrd
    jca
    cA
    cY
    cP
    cQ
    cR
    cT
    cS
    cU
    cG
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cD
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.u
    cdleme19.g
    cdleme19.f
    cdleme19.y
    cdleme19.d
    cdleme19d
    syl333anc
    3eqtr4d
end
