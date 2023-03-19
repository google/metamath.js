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
include "simp12l.mm"
include "simp13l.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "3eqtr4g.mm"
include "oveq2d.mm"
include "simp11.mm"
include "simp13.mm"
include "simp12.mm"
include "simp21.mm"
include "necomd.mm"
include "simp23.mm"
include "simp3r.mm"
include "breq2d.mm"
include "mtbid.mm"
include "cdleme35g.mm"
include "syl321anc.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "eqcomd.mm"

theorem cdleme43dN
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) ) ) -> ( Z .\/ S ) = ( Z .\/ E ) )

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
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    cS
    @14
    c.le
    wbr
    #
    wn
    #
    wa
    #
    w3a
    #
    cZ
    cE
    c.or
    co
    cZ
    cS
    c.or
    co
    @19
    cE
    cS
    cZ
    c.or
    @19
    cE
    cD
    cU
    c.or
    co
    #
    cQ
    cP
    cD
    c.or
    co
    cW
    c.an
    co
    c.or
    co
    #
    c.an
    co
    #
    cS
    cdleme43.e
    @19
    @22
    cD
    cX
    c.or
    co
    #
    @21
    c.an
    co
    #
    cS
    @19
    @20
    @23
    @21
    c.an
    @19
    cU
    cX
    cD
    c.or
    @19
    @14
    cW
    c.an
    co
    cQ
    cP
    c.or
    co
    #
    cW
    c.an
    co
    cU
    cX
    @19
    @14
    @25
    cW
    c.an
    @19
    @0
    @3
    @6
    @14
    @25
    wceq
    @0
    @1
    @5
    @8
    @13
    @18
    simp11l
    @3
    @4
    @2
    @8
    @13
    @18
    simp12l
    @6
    @7
    @2
    @5
    @13
    @18
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
    #
    oveq1d
    cdleme43.u
    cdleme43.x
    3eqtr4g
    oveq2d
    oveq1d
    @19
    @2
    @8
    @5
    cQ
    cP
    wne
    @12
    cS
    @25
    c.le
    wbr
    #
    wn
    @24
    cS
    wceq
    @2
    @5
    @8
    @13
    @18
    simp11
    @2
    @5
    @8
    @13
    @18
    simp13
    @2
    @5
    @8
    @13
    @18
    simp12
    @19
    cP
    cQ
    @9
    @10
    @11
    @12
    @18
    simp21
    necomd
    @9
    @10
    @11
    @12
    @18
    simp23
    @19
    @16
    @27
    @9
    @13
    @15
    @17
    simp3r
    @19
    @14
    @25
    cS
    c.le
    @26
    breq2d
    mtbid
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
    cdleme35g
    syl321anc
    eqtrd
    syl5eq
    oveq2d
    eqcomd
end
