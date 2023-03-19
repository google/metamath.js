include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "simpl11.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl23.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "simpr.mm"
include "cdleme11.mm"
include "syl333anc.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "cdleme16g.mm"
include "pm2.61dan.mm"

theorem cdleme16
  let cA: class A
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
  assume cdleme12.l: |- .<_ = ( le ` K )
  assume cdleme12.j: |- .\/ = ( join ` K )
  assume cdleme12.m: |- ./\ = ( meet ` K )
  assume cdleme12.a: |- A = ( Atoms ` K )
  assume cdleme12.h: |- H = ( LHyp ` K )
  assume cdleme12.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme12.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme12.g: |- G = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( P =/= Q /\ S =/= T ) ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) ) ) -> ( ( S .\/ T ) ./\ W ) = ( ( F .\/ G ) ./\ W ) )

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
    cP
    cQ
    wne
    cS
    cT
    wne
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
    @8
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
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
    @13
    cW
    c.an
    co
    cF
    cG
    c.or
    co
    #
    cW
    c.an
    co
    wceq
    #
    @12
    @14
    wa
    #
    @13
    @15
    cW
    c.an
    @17
    @15
    @13
    @17
    @0
    @1
    @2
    @4
    @5
    @6
    @9
    @10
    @14
    @15
    @13
    wceq
    @0
    @1
    @2
    @7
    @11
    @14
    simpl11
    @0
    @1
    @2
    @7
    @11
    @14
    simpl12
    @0
    @1
    @2
    @7
    @11
    @14
    simpl13
    @4
    @5
    @6
    @3
    @11
    @14
    simpl21
    @4
    @5
    @6
    @3
    @11
    @14
    simpl22
    @4
    @5
    @6
    @3
    @11
    @14
    simpl23
    @9
    @10
    @3
    @7
    @14
    simpl3l
    @9
    @10
    @3
    @7
    @14
    simpl3r
    @12
    @14
    simpr
    cA
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
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    cdleme12.h
    cdleme12.u
    cdleme12.f
    cdleme12.g
    cdleme11
    syl333anc
    eqcomd
    oveq1d
    @12
    @14
    wn
    #
    wa
    @0
    @1
    @2
    @4
    @5
    @6
    @9
    @10
    @18
    @16
    @0
    @1
    @2
    @7
    @11
    @18
    simpl11
    @0
    @1
    @2
    @7
    @11
    @18
    simpl12
    @0
    @1
    @2
    @7
    @11
    @18
    simpl13
    @4
    @5
    @6
    @3
    @11
    @18
    simpl21
    @4
    @5
    @6
    @3
    @11
    @18
    simpl22
    @4
    @5
    @6
    @3
    @11
    @18
    simpl23
    @9
    @10
    @3
    @7
    @18
    simpl3l
    @9
    @10
    @3
    @7
    @18
    simpl3r
    @12
    @18
    simpr
    cA
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
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    cdleme12.h
    cdleme12.u
    cdleme12.f
    cdleme12.g
    cdleme16g
    syl333anc
    pm2.61dan
end
