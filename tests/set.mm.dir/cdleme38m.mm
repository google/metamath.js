include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "simp1.mm"
include "simp2.mm"
include "simp311.mm"
include "simp312.mm"
include "simp313.mm"
include "jca.mm"
include "simp32.mm"
include "simp33.mm"
include "eqid.mm"
include "cdleme37m.mm"
include "syl113anc.mm"
include "eqtr4d.mm"
include "3jca.mm"
include "cbs.mm"
include "cfv.mm"
include "cdleme36m.mm"
include "syl112anc.mm"

theorem cdleme38m
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  let cX: class X
  assume cdleme38.l: |- .<_ = ( le ` K )
  assume cdleme38.j: |- .\/ = ( join ` K )
  assume cdleme38.m: |- ./\ = ( meet ` K )
  assume cdleme38.a: |- A = ( Atoms ` K )
  assume cdleme38.h: |- H = ( LHyp ` K )
  assume cdleme38.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme38.e: |- E = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdleme38.d: |- D = ( ( u .\/ U ) ./\ ( Q .\/ ( ( P .\/ u ) ./\ W ) ) )
  assume cdleme38.v: |- V = ( ( t .\/ E ) ./\ W )
  assume cdleme38.x: |- X = ( ( u .\/ D ) ./\ W )
  assume cdleme38.f: |- F = ( ( R .\/ V ) ./\ ( E .\/ ( ( t .\/ R ) ./\ W ) ) )
  assume cdleme38.g: |- G = ( ( S .\/ X ) ./\ ( D .\/ ( ( u .\/ S ) ./\ W ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( ( R .<_ ( P .\/ Q ) /\ S .<_ ( P .\/ Q ) /\ F = G ) /\ ( ( t e. A /\ -. t .<_ W ) /\ -. t .<_ ( P .\/ Q ) ) /\ ( ( u e. A /\ -. u .<_ W ) /\ -. u .<_ ( P .\/ Q ) ) ) ) -> R = S )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    w3a
    #
    cP
    cQ
    wne
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    cS
    cA
    wcel
    cS
    cW
    c.le
    wbr
    wn
    wa
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
    @2
    c.le
    wbr
    #
    cF
    cG
    wceq
    #
    w3a
    #
    vt
    cv
    #
    cA
    wcel
    @7
    cW
    c.le
    wbr
    wn
    wa
    @7
    @2
    c.le
    wbr
    wn
    wa
    #
    vu
    cv
    #
    cA
    wcel
    @9
    cW
    c.le
    wbr
    wn
    wa
    @9
    @2
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    w3a
    #
    @0
    @1
    @3
    @4
    cF
    cS
    cV
    c.or
    co
    cE
    @7
    cS
    c.or
    co
    cW
    c.an
    co
    c.or
    co
    c.an
    co
    #
    wceq
    #
    w3a
    @8
    cR
    cS
    wceq
    @0
    @1
    @11
    simp1
    #
    @0
    @1
    @11
    simp2
    #
    @12
    @3
    @4
    @14
    @3
    @4
    @5
    @8
    @10
    @0
    @1
    simp311
    #
    @3
    @4
    @5
    @8
    @10
    @0
    @1
    simp312
    #
    @12
    cF
    cG
    @13
    @3
    @4
    @5
    @8
    @10
    @0
    @1
    simp313
    @12
    @0
    @1
    @3
    @4
    wa
    @8
    @10
    @13
    cG
    wceq
    @15
    @16
    @12
    @3
    @4
    @17
    @18
    jca
    @0
    @1
    @6
    @8
    @10
    simp32
    #
    @0
    @1
    @6
    @8
    @10
    simp33
    vu
    vt
    cA
    @13
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
    cdleme38.l
    cdleme38.j
    cdleme38.m
    cdleme38.a
    cdleme38.h
    cdleme38.u
    cdleme38.e
    cdleme38.d
    cdleme38.v
    cdleme38.x
    @13
    eqid
    #
    cdleme38.g
    cdleme37m
    syl113anc
    eqtr4d
    3jca
    @19
    vt
    cA
    cK
    cbs
    cfv
    #
    @13
    cP
    cQ
    cR
    cS
    cU
    cE
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    @21
    eqid
    cdleme38.l
    cdleme38.j
    cdleme38.m
    cdleme38.a
    cdleme38.h
    cdleme38.u
    cdleme38.e
    cdleme38.v
    cdleme38.f
    @20
    cdleme36m
    syl112anc
end
