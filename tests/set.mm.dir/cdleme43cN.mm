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
include "simp22.mm"
include "simp1.mm"
include "simp21.mm"
include "simp23.mm"
include "simp3.mm"
include "cdleme43bN.mm"
include "syl121anc.mm"
include "cdleme42a.mm"
include "syl3anc.mm"

theorem cdleme43cN
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ -. S .<_ ( P .\/ Q ) ) -> ( R .\/ D ) = ( R .\/ Y ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    cP
    cQ
    wne
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
    cS
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cS
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    #
    w3a
    #
    @0
    @5
    cD
    cA
    wcel
    cD
    cW
    c.le
    wbr
    wn
    wa
    #
    cR
    cD
    c.or
    co
    cR
    cY
    c.or
    co
    wceq
    @0
    @1
    @2
    @7
    @8
    simp11
    @3
    @4
    @5
    @6
    @8
    simp22
    @9
    @3
    @4
    @6
    @8
    @10
    @3
    @7
    @8
    simp1
    @3
    @4
    @5
    @6
    @8
    simp21
    @3
    @4
    @5
    @6
    @8
    simp23
    @3
    @7
    @8
    simp3
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    cS
    cU
    cE
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cX
    cY
    cZ
    cdleme43.b
    cdleme43.l
    cdleme43.j
    cdleme43.m
    cdleme43.a
    cdleme43.h
    cdleme43.u
    cdleme43.x
    cdleme43.c
    cdleme43.f
    cdleme43.d
    cdleme43.g
    cdleme43.e
    cdleme43.v
    cdleme43.y
    cdleme43bN
    syl121anc
    cA
    cB
    cR
    cD
    cH
    c.or
    cK
    c.le
    c.an
    cY
    cW
    cdleme43.b
    cdleme43.l
    cdleme43.j
    cdleme43.m
    cdleme43.a
    cdleme43.h
    cdleme43.y
    cdleme42a
    syl3anc
end
