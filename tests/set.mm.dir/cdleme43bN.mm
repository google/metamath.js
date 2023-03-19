include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "simp11.mm"
include "simp13.mm"
include "simp12.mm"
include "simp2r.mm"
include "simp2l.mm"
include "necomd.mm"
include "simp3.mm"
include "wceq.mm"
include "simp11l.mm"
include "simp12l.mm"
include "simp13l.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "breq2d.mm"
include "mtbid.mm"
include "cdleme3fa.mm"
include "syl132anc.mm"
include "cdleme3.mm"
include "jca.mm"

theorem cdleme43bN
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cE: class E
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume cdleme43.b: |- B = ( Base ` K )
  assume cdleme43.l: |- .<_ = ( le ` K )
  assume cdleme43.j: |- .\/ = ( join ` K )
  assume cdleme43.m: |- ./\ = ( meet ` K )
  assume cdleme43.a: |- A = ( Atoms ` K )
  assume cdleme43.h: |- H = ( LHyp ` K )
  assume cdleme43.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme43.x: |- X = ( ( Q .\/ P ) ./\ W )
  assume cdleme43.c: |- C = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme43.f: |- Z = ( ( P .\/ Q ) ./\ ( C .\/ ( ( R .\/ S ) ./\ W ) ) )
  assume cdleme43.d: |- D = ( ( S .\/ X ) ./\ ( P .\/ ( ( Q .\/ S ) ./\ W ) ) )
  assume cdleme43.g: |- G = ( ( Q .\/ P ) ./\ ( D .\/ ( ( Z .\/ S ) ./\ W ) ) )
  assume cdleme43.e: |- E = ( ( D .\/ U ) ./\ ( Q .\/ ( ( P .\/ D ) ./\ W ) ) )
  assume cdleme43.v: |- V = ( ( Z .\/ S ) ./\ W )
  assume cdleme43.y: |- Y = ( ( R .\/ D ) ./\ W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( S e. A /\ -. S .<_ W ) ) /\ -. S .<_ ( P .\/ Q ) ) -> ( D e. A /\ -. D .<_ W ) )

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
    cP
    cQ
    wne
    #
    cS
    cA
    wcel
    cS
    cW
    c.le
    wbr
    wn
    wa
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
    #
    wn
    #
    w3a
    #
    cD
    cA
    wcel
    #
    cD
    cW
    c.le
    wbr
    wn
    #
    @16
    @2
    @8
    @5
    @11
    cQ
    cP
    wne
    #
    cS
    cQ
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    @17
    @2
    @5
    @8
    @12
    @15
    simp11
    #
    @2
    @5
    @8
    @12
    @15
    simp13
    #
    @2
    @5
    @8
    @12
    @15
    simp12
    #
    @9
    @10
    @11
    @15
    simp2r
    #
    @16
    cP
    cQ
    @9
    @10
    @11
    @15
    simp2l
    necomd
    #
    @16
    @14
    @21
    @9
    @12
    @15
    simp3
    @16
    @13
    @20
    cS
    c.le
    @16
    @0
    @3
    @6
    @13
    @20
    wceq
    @0
    @1
    @5
    @8
    @12
    @15
    simp11l
    @3
    @4
    @2
    @8
    @12
    @15
    simp12l
    @6
    @7
    @2
    @5
    @12
    @15
    simp13l
    cA
    c.or
    cK
    cP
    cQ
    cdleme43.j
    cdleme43.a
    hlatjcom
    syl3anc
    breq2d
    mtbid
    #
    cA
    cQ
    cP
    cS
    cX
    cD
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme43.l
    cdleme43.j
    cdleme43.m
    cdleme43.a
    cdleme43.h
    cdleme43.x
    cdleme43.d
    cdleme3fa
    syl132anc
    @16
    @2
    @8
    @5
    @11
    @19
    @22
    @18
    @23
    @24
    @25
    @26
    @27
    @28
    cA
    cQ
    cP
    cS
    cX
    cD
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme43.l
    cdleme43.j
    cdleme43.m
    cdleme43.a
    cdleme43.h
    cdleme43.x
    cdleme43.d
    cdleme3
    syl132anc
    jca
end
