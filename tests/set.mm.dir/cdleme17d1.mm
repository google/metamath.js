include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "eqid.mm"
include "cdleme17a.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp21l.mm"
include "simp21r.mm"
include "simp22.mm"
include "simp23l.mm"
include "simp3.mm"
include "cdleme17c.mm"
include "syl223anc.mm"
include "eqtrd.mm"

theorem cdleme17d1
  let cA: class A
  let cP: class P
  let cQ: class Q
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
  assume cdleme17.l: |- .<_ = ( le ` K )
  assume cdleme17.j: |- .\/ = ( join ` K )
  assume cdleme17.m: |- ./\ = ( meet ` K )
  assume cdleme17.a: |- A = ( Atoms ` K )
  assume cdleme17.h: |- H = ( LHyp ` K )
  assume cdleme17.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme17.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme17.g: |- G = ( ( P .\/ Q ) ./\ ( F .\/ ( ( P .\/ S ) ./\ W ) ) )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ Q e. A /\ ( S e. A /\ -. S .<_ W ) ) /\ -. S .<_ ( P .\/ Q ) ) -> G = Q )

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
    w3a
    #
    cG
    @11
    cQ
    cP
    cS
    c.or
    co
    cW
    c.an
    co
    #
    c.or
    co
    c.an
    co
    #
    cQ
    cA
    @14
    cP
    cQ
    cS
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme17.l
    cdleme17.j
    cdleme17.m
    cdleme17.a
    cdleme17.h
    cdleme17.u
    cdleme17.f
    cdleme17.g
    @14
    eqid
    #
    cdleme17a
    @13
    @0
    @1
    @3
    @4
    @6
    @7
    @12
    @15
    cQ
    wceq
    @0
    @1
    @10
    @12
    simp1l
    @0
    @1
    @10
    @12
    simp1r
    @3
    @4
    @6
    @9
    @2
    @12
    simp21l
    @3
    @4
    @6
    @9
    @2
    @12
    simp21r
    @2
    @5
    @6
    @9
    @12
    simp22
    @7
    @8
    @5
    @6
    @2
    @12
    simp23l
    @2
    @10
    @12
    simp3
    cA
    @14
    cP
    cQ
    cS
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme17.l
    cdleme17.j
    cdleme17.m
    cdleme17.a
    cdleme17.h
    cdleme17.u
    cdleme17.f
    cdleme17.g
    @16
    cdleme17c
    syl223anc
    eqtrd
end
