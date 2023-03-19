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
include "simp12l.mm"
include "simp12r.mm"
include "simp22l.mm"
include "cdleme8.mm"
include "syl221anc.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "eqtr2d.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp22.mm"
include "simp23l.mm"
include "simp32.mm"
include "cdleme3fa.mm"
include "syl132anc.mm"
include "simp13l.mm"
include "cdleme11g.mm"
include "syl131anc.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "simp21l.mm"
include "eqcomd.mm"

theorem cdleme15a
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
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
  let cX: class X
  assume cdleme12.l: |- .<_ = ( le ` K )
  assume cdleme12.j: |- .\/ = ( join ` K )
  assume cdleme12.m: |- ./\ = ( meet ` K )
  assume cdleme12.a: |- A = ( Atoms ` K )
  assume cdleme12.h: |- H = ( LHyp ` K )
  assume cdleme12.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme12.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme12.g: |- G = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )
  assume cdleme15.c: |- C = ( ( P .\/ S ) ./\ W )
  assume cdleme15.x: |- X = ( ( P .\/ T ) ./\ W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( P =/= Q /\ S =/= T ) ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) /\ -. U .<_ ( S .\/ T ) ) ) -> ( ( ( T .\/ P ) ./\ ( G .\/ Q ) ) .\/ ( ( P .\/ S ) ./\ ( Q .\/ F ) ) ) = ( ( ( P .\/ X ) ./\ ( Q .\/ X ) ) .\/ ( ( P .\/ C ) ./\ ( Q .\/ C ) ) ) )

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
    w3a
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
    @20
    c.le
    wbr
    wn
    #
    cU
    cS
    cT
    c.or
    co
    c.le
    wbr
    wn
    #
    w3a
    #
    w3a
    #
    cT
    cP
    c.or
    co
    #
    cG
    cQ
    c.or
    co
    #
    c.an
    co
    cP
    cX
    c.or
    co
    #
    cQ
    cX
    c.or
    co
    #
    c.an
    co
    cP
    cS
    c.or
    co
    #
    cQ
    cF
    c.or
    co
    #
    c.an
    co
    cP
    cC
    c.or
    co
    #
    cQ
    cC
    c.or
    co
    #
    c.an
    co
    c.or
    @25
    @26
    @28
    @27
    @29
    c.an
    @25
    @28
    cP
    cT
    c.or
    co
    #
    @26
    @25
    @0
    @1
    @3
    @4
    @13
    @28
    @34
    wceq
    @0
    @1
    @5
    @8
    @19
    @24
    simp11l
    #
    @0
    @1
    @5
    @8
    @19
    @24
    simp11r
    #
    @3
    @4
    @2
    @8
    @19
    @24
    simp12l
    #
    @3
    @4
    @2
    @8
    @19
    @24
    simp12r
    #
    @13
    @14
    @12
    @18
    @9
    @24
    simp22l
    #
    cA
    cX
    cP
    cT
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    cdleme12.h
    cdleme15.x
    cdleme8
    syl221anc
    @25
    @0
    @3
    @13
    @34
    @26
    wceq
    @35
    @37
    @39
    cA
    c.or
    cK
    cP
    cT
    cdleme12.j
    cdleme12.a
    hlatjcom
    syl3anc
    eqtr2d
    @25
    @27
    cQ
    cG
    c.or
    co
    #
    @29
    @25
    @0
    cG
    cA
    wcel
    #
    @6
    @27
    @40
    wceq
    @35
    @25
    @2
    @5
    @8
    @15
    @16
    @22
    @41
    @2
    @5
    @8
    @19
    @24
    simp11
    #
    @2
    @5
    @8
    @19
    @24
    simp12
    @2
    @5
    @8
    @19
    @24
    simp13
    #
    @9
    @12
    @15
    @18
    @24
    simp22
    @16
    @17
    @12
    @15
    @9
    @24
    simp23l
    #
    @9
    @19
    @21
    @22
    @23
    simp32
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
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    cdleme12.h
    cdleme12.u
    cdleme12.g
    cdleme3fa
    syl132anc
    @6
    @7
    @2
    @5
    @19
    @24
    simp13l
    cA
    c.or
    cK
    cG
    cQ
    cdleme12.j
    cdleme12.a
    hlatjcom
    syl3anc
    @25
    @2
    @3
    @8
    @13
    @16
    @40
    @29
    wceq
    @42
    @37
    @43
    @39
    @44
    cA
    cX
    cU
    cP
    cQ
    cT
    cQ
    cU
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    cdleme12.h
    cdleme12.u
    cdleme15.x
    cdleme12.u
    cdleme12.g
    cdleme11g
    syl131anc
    eqtrd
    oveq12d
    @25
    @30
    @32
    @31
    @33
    c.an
    @25
    @32
    @30
    @25
    @0
    @1
    @3
    @4
    @10
    @32
    @30
    wceq
    @35
    @36
    @37
    @38
    @10
    @11
    @15
    @18
    @9
    @24
    simp21l
    #
    cA
    cC
    cP
    cS
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    cdleme12.h
    cdleme15.c
    cdleme8
    syl221anc
    eqcomd
    @25
    @2
    @3
    @8
    @10
    @16
    @31
    @33
    wceq
    @42
    @37
    @43
    @45
    @44
    cA
    cC
    cU
    cP
    cQ
    cS
    cQ
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    cdleme12.h
    cdleme12.u
    cdleme15.c
    cdleme12.u
    cdleme12.f
    cdleme11g
    syl131anc
    oveq12d
    oveq12d
end
