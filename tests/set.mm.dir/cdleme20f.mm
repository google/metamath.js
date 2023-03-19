include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cdleme20e.mm"
include "wi.mm"
include "simp11l.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21.mm"
include "simp31l.mm"
include "simp32l.mm"
include "cdleme3fa.mm"
include "syl132anc.mm"
include "simp11r.mm"
include "simp21l.mm"
include "simp21r.mm"
include "simp23l.mm"
include "simp33.mm"
include "cdlemeda.mm"
include "syl223anc.mm"
include "simp22.mm"
include "simp32r.mm"
include "simp22l.mm"
include "simp22r.mm"
include "dalaw.mm"
include "syl133anc.mm"
include "mpd.mm"

theorem cdleme20f
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) /\ ( ( P =/= Q /\ S =/= T ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) ) /\ R .<_ ( P .\/ Q ) ) ) -> ( ( F .\/ D ) ./\ ( G .\/ Y ) ) .<_ ( ( ( D .\/ S ) ./\ ( Y .\/ T ) ) .\/ ( ( S .\/ F ) ./\ ( T .\/ G ) ) ) )

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
    w3a
    #
    w3a
    #
    cF
    cG
    c.or
    co
    cD
    cY
    c.or
    co
    c.an
    co
    cS
    cT
    c.or
    co
    c.le
    wbr
    #
    cF
    cD
    c.or
    co
    cG
    cY
    c.or
    co
    c.an
    co
    cD
    cS
    c.or
    co
    cY
    cT
    c.or
    co
    c.an
    co
    cS
    cF
    c.or
    co
    cT
    cG
    c.or
    co
    c.an
    co
    c.or
    co
    c.le
    wbr
    #
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
    cV
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
    cdleme20.v
    cdleme20e
    @25
    @0
    cF
    cA
    wcel
    #
    cD
    cA
    wcel
    #
    @6
    cG
    cA
    wcel
    #
    cY
    cA
    wcel
    #
    @9
    @26
    @27
    wi
    @0
    @1
    @3
    @4
    @15
    @24
    simp11l
    #
    @25
    @2
    @3
    @4
    @8
    @16
    @20
    @28
    @2
    @3
    @4
    @15
    @24
    simp11
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
    @8
    @11
    @14
    @24
    simp21
    @16
    @17
    @22
    @23
    @5
    @15
    simp31l
    #
    @20
    @21
    @18
    @23
    @5
    @15
    simp32l
    #
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
    cdleme3fa
    syl132anc
    @25
    @0
    @1
    @6
    @7
    @12
    @23
    @20
    @29
    @32
    @0
    @1
    @3
    @4
    @15
    @24
    simp11r
    #
    @6
    @7
    @11
    @14
    @5
    @24
    simp21l
    #
    @6
    @7
    @11
    @14
    @5
    @24
    simp21r
    @12
    @13
    @8
    @11
    @5
    @24
    simp23l
    #
    @5
    @15
    @18
    @22
    @23
    simp33
    #
    @37
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
    @39
    @25
    @2
    @3
    @4
    @11
    @16
    @21
    @30
    @33
    @34
    @35
    @5
    @8
    @11
    @14
    @24
    simp22
    @36
    @20
    @21
    @18
    @23
    @5
    @15
    simp32r
    #
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
    cdleme3fa
    syl132anc
    @25
    @0
    @1
    @9
    @10
    @12
    @23
    @21
    @31
    @32
    @38
    @9
    @10
    @8
    @14
    @5
    @24
    simp22l
    #
    @9
    @10
    @8
    @14
    @5
    @24
    simp22r
    @40
    @41
    @42
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
    @43
    cA
    cF
    cD
    cS
    cG
    cY
    cT
    c.or
    cK
    c.le
    c.an
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    dalaw
    syl133anc
    mpd
end
