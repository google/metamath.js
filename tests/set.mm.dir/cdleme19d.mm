include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "cdleme19b.mm"
include "clc.mm"
include "wb.mm"
include "simp11l.mm"
include "hlcvl.mm"
include "syl.mm"
include "simp11r.mm"
include "simp21l.mm"
include "simp21r.mm"
include "simp23.mm"
include "simp33l.mm"
include "simp32l.mm"
include "cdlemeda.mm"
include "syl223anc.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp22.mm"
include "simp31l.mm"
include "simp32r.mm"
include "cdleme3fa.mm"
include "syl132anc.mm"
include "simp21.mm"
include "cdleme19c.mm"
include "syl233anc.mm"
include "necomd.mm"
include "cvlatexchb1.mm"
include "syl131anc.mm"
include "mpbid.mm"

theorem cdleme19d
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ R e. A ) /\ ( ( P =/= Q /\ S =/= T ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) ) /\ ( R .<_ ( P .\/ Q ) /\ R .<_ ( S .\/ T ) ) ) ) -> ( F .\/ D ) = ( F .\/ G ) )

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
    cT
    cW
    c.le
    wbr
    wn
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
    @15
    c.le
    wbr
    wn
    #
    wa
    #
    cR
    @15
    c.le
    wbr
    #
    cR
    cS
    cT
    c.or
    co
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
    c.le
    wbr
    #
    cF
    cD
    c.or
    co
    @24
    wceq
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
    cdleme19b
    @23
    cK
    clc
    wcel
    #
    cD
    cA
    wcel
    #
    cG
    cA
    wcel
    #
    cF
    cA
    wcel
    #
    cD
    cF
    wne
    @25
    @26
    wb
    @23
    @0
    @27
    @0
    @1
    @3
    @4
    @11
    @22
    simp11l
    #
    cK
    hlcvl
    syl
    @23
    @0
    @1
    @6
    @7
    @10
    @19
    @16
    @28
    @31
    @0
    @1
    @3
    @4
    @11
    @22
    simp11r
    #
    @6
    @7
    @9
    @10
    @5
    @22
    simp21l
    @6
    @7
    @9
    @10
    @5
    @22
    simp21r
    @5
    @8
    @9
    @10
    @22
    simp23
    #
    @19
    @20
    @14
    @18
    @5
    @11
    simp33l
    @16
    @17
    @14
    @21
    @5
    @11
    simp32l
    #
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
    @23
    @2
    @3
    @4
    @9
    @12
    @17
    @29
    @2
    @3
    @4
    @11
    @22
    simp11
    #
    @2
    @3
    @4
    @11
    @22
    simp12
    #
    @2
    @3
    @4
    @11
    @22
    simp13
    #
    @5
    @8
    @9
    @10
    @22
    simp22
    @12
    @13
    @18
    @21
    @5
    @11
    simp31l
    #
    @16
    @17
    @14
    @21
    @5
    @11
    simp32r
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
    @23
    @2
    @3
    @4
    @8
    @12
    @16
    @30
    @35
    @36
    @37
    @5
    @8
    @9
    @10
    @22
    simp21
    #
    @38
    @34
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
    @23
    cF
    cD
    @23
    @0
    @1
    @3
    @4
    @8
    @10
    @12
    @16
    cF
    cD
    wne
    @31
    @32
    @36
    @37
    @39
    @33
    @38
    @34
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
    cdleme19c
    syl233anc
    necomd
    cA
    cD
    cG
    cF
    c.or
    cK
    c.le
    cdleme19.l
    cdleme19.j
    cdleme19.a
    cvlatexchb1
    syl131anc
    mpbid
end
