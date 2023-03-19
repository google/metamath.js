include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cv.mm"
include "simp313.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl23.mm"
include "simp311.mm"
include "adantr.mm"
include "simp312.mm"
include "simpr.mm"
include "3jca.mm"
include "simpl32.mm"
include "simpl33.mm"
include "cdleme38m.mm"
include "syl133anc.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"

theorem cdleme38n
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( ( R .<_ ( P .\/ Q ) /\ S .<_ ( P .\/ Q ) /\ R =/= S ) /\ ( ( t e. A /\ -. t .<_ W ) /\ -. t .<_ ( P .\/ Q ) ) /\ ( ( u e. A /\ -. u .<_ W ) /\ -. u .<_ ( P .\/ Q ) ) ) ) -> F =/= G )

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
    @5
    c.le
    wbr
    #
    cR
    cS
    wne
    #
    w3a
    #
    vt
    cv
    #
    cA
    wcel
    @10
    cW
    c.le
    wbr
    wn
    wa
    @10
    @5
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
    @12
    cW
    c.le
    wbr
    wn
    wa
    @12
    @5
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    w3a
    #
    @8
    cF
    cG
    wne
    @6
    @7
    @8
    @11
    @13
    @0
    @4
    simp313
    @15
    cF
    cG
    cR
    cS
    @15
    cF
    cG
    wceq
    #
    cR
    cS
    wceq
    #
    @15
    @16
    wa
    #
    @0
    @1
    @2
    @3
    @6
    @7
    @16
    w3a
    @11
    @13
    @17
    @0
    @4
    @14
    @16
    simpl1
    @1
    @2
    @3
    @0
    @14
    @16
    simpl21
    @1
    @2
    @3
    @0
    @14
    @16
    simpl22
    @1
    @2
    @3
    @0
    @14
    @16
    simpl23
    @18
    @6
    @7
    @16
    @15
    @6
    @16
    @6
    @7
    @8
    @11
    @13
    @0
    @4
    simp311
    adantr
    @15
    @7
    @16
    @6
    @7
    @8
    @11
    @13
    @0
    @4
    simp312
    adantr
    @15
    @16
    simpr
    3jca
    @9
    @11
    @13
    @0
    @4
    @16
    simpl32
    @9
    @11
    @13
    @0
    @4
    @16
    simpl33
    vu
    vt
    cA
    cD
    cP
    cQ
    cR
    cS
    cU
    cE
    cF
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
    cdleme38.f
    cdleme38.g
    cdleme38m
    syl133anc
    ex
    necon3d
    mpd
end
