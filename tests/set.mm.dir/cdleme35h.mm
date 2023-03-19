include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "3ad2ant3.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "simp31.mm"
include "cdleme35g.mm"
include "syl121anc.mm"
include "simp23.mm"
include "simp32.mm"
include "3eqtr3d.mm"

theorem cdleme35h
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme35.l: |- .<_ = ( le ` K )
  assume cdleme35.j: |- .\/ = ( join ` K )
  assume cdleme35.m: |- ./\ = ( meet ` K )
  assume cdleme35.a: |- A = ( Atoms ` K )
  assume cdleme35.h: |- H = ( LHyp ` K )
  assume cdleme35.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme35.f: |- F = ( ( R .\/ U ) ./\ ( Q .\/ ( ( P .\/ R ) ./\ W ) ) )
  assume cdleme35.g: |- G = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( -. R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) /\ F = G ) ) -> R = S )

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
    wn
    #
    cS
    @5
    c.le
    wbr
    wn
    #
    cF
    cG
    wceq
    #
    w3a
    #
    w3a
    #
    cF
    cU
    c.or
    co
    #
    cP
    cQ
    cF
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    #
    cG
    cU
    c.or
    co
    #
    cP
    cQ
    cG
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    #
    cR
    cS
    @9
    @0
    @15
    @20
    wceq
    #
    @4
    @8
    @6
    @21
    @7
    @8
    @11
    @16
    @14
    @19
    c.an
    cF
    cG
    cU
    c.or
    oveq1
    @8
    @13
    @18
    cP
    c.or
    @8
    @12
    @17
    cW
    c.an
    cF
    cG
    cQ
    c.or
    oveq2
    oveq1d
    oveq2d
    oveq12d
    3ad2ant3
    3ad2ant3
    @10
    @0
    @1
    @2
    @6
    @15
    cR
    wceq
    @0
    @4
    @9
    simp1
    #
    @0
    @1
    @2
    @3
    @9
    simp21
    #
    @0
    @1
    @2
    @3
    @9
    simp22
    @0
    @4
    @6
    @7
    @8
    simp31
    cA
    cP
    cQ
    cR
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme35.l
    cdleme35.j
    cdleme35.m
    cdleme35.a
    cdleme35.h
    cdleme35.u
    cdleme35.f
    cdleme35g
    syl121anc
    @10
    @0
    @1
    @3
    @7
    @20
    cS
    wceq
    @22
    @23
    @0
    @1
    @2
    @3
    @9
    simp23
    @0
    @4
    @6
    @7
    @8
    simp32
    cA
    cP
    cQ
    cS
    cU
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme35.l
    cdleme35.j
    cdleme35.m
    cdleme35.a
    cdleme35.h
    cdleme35.u
    cdleme35.g
    cdleme35g
    syl121anc
    3eqtr3d
end
