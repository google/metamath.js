include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp22.mm"
include "simp21.mm"
include "simp23l.mm"
include "simp23r.mm"
include "necomd.mm"
include "jca.mm"
include "simp32.mm"
include "simp31.mm"
include "simp33.mm"
include "simp11l.mm"
include "simp21l.mm"
include "simp22l.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "breq2d.mm"
include "mtbid.mm"
include "cdleme15b.mm"
include "syl333anc.mm"
include "oveq12d.mm"

theorem cdleme15c
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( P =/= Q /\ S =/= T ) ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) /\ -. U .<_ ( S .\/ T ) ) ) -> ( ( ( P .\/ X ) ./\ ( Q .\/ X ) ) .\/ ( ( P .\/ C ) ./\ ( Q .\/ C ) ) ) = ( X .\/ C ) )

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
    @16
    c.le
    wbr
    wn
    #
    cU
    cS
    cT
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    w3a
    #
    w3a
    #
    cP
    cX
    c.or
    co
    cQ
    cX
    c.or
    co
    c.an
    co
    #
    cX
    cP
    cC
    c.or
    co
    cQ
    cC
    c.or
    co
    c.an
    co
    cC
    c.or
    @23
    @2
    @3
    @4
    @11
    @8
    @12
    cT
    cS
    wne
    #
    wa
    @18
    @17
    cU
    cT
    cS
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    @24
    cX
    wceq
    @2
    @3
    @4
    @15
    @22
    simp11
    @2
    @3
    @4
    @15
    @22
    simp12
    @2
    @3
    @4
    @15
    @22
    simp13
    @5
    @8
    @11
    @14
    @22
    simp22
    @5
    @8
    @11
    @14
    @22
    simp21
    @23
    @12
    @25
    @12
    @13
    @8
    @11
    @5
    @22
    simp23l
    @23
    cS
    cT
    @12
    @13
    @8
    @11
    @5
    @22
    simp23r
    necomd
    jca
    @5
    @15
    @17
    @18
    @21
    simp32
    @5
    @15
    @17
    @18
    @21
    simp31
    @23
    @20
    @27
    @5
    @15
    @17
    @18
    @21
    simp33
    @23
    @19
    @26
    cU
    c.le
    @23
    @0
    @6
    @9
    @19
    @26
    wceq
    @0
    @1
    @3
    @4
    @15
    @22
    simp11l
    @6
    @7
    @11
    @14
    @5
    @22
    simp21l
    @9
    @10
    @8
    @14
    @5
    @22
    simp22l
    cA
    c.or
    cK
    cS
    cT
    cdleme12.j
    cdleme12.a
    hlatjcom
    syl3anc
    breq2d
    mtbid
    cA
    cX
    cP
    cQ
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
    cC
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    cdleme12.h
    cdleme12.u
    cdleme12.g
    cdleme12.f
    cdleme15.x
    cdleme15.c
    cdleme15b
    syl333anc
    cA
    cC
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
    cX
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    cdleme12.h
    cdleme12.u
    cdleme12.f
    cdleme12.g
    cdleme15.c
    cdleme15.x
    cdleme15b
    oveq12d
end
