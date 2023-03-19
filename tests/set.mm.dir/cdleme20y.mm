include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wceq.mm"
include "simp1.mm"
include "simp22.mm"
include "simp23.mm"
include "simp21.mm"
include "simp3.mm"
include "2llnma2rN.mm"
include "syl131anc.mm"

theorem cdleme20y
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  assume cdleme20z.l: |- .<_ = ( le ` K )
  assume cdleme20z.j: |- .\/ = ( join ` K )
  assume cdleme20z.m: |- ./\ = ( meet ` K )
  assume cdleme20z.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( R e. A /\ S e. A /\ T e. A ) /\ ( S =/= T /\ -. R .<_ ( S .\/ T ) ) ) -> ( ( S .\/ R ) ./\ ( T .\/ R ) ) = R )

  proof
    cK
    chlt
    wcel
    #
    cR
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    cT
    cA
    wcel
    #
    w3a
    #
    cS
    cT
    wne
    cR
    cS
    cT
    c.or
    co
    c.le
    wbr
    wn
    wa
    #
    w3a
    @0
    @2
    @3
    @1
    @5
    cS
    cR
    c.or
    co
    cT
    cR
    c.or
    co
    c.an
    co
    cR
    wceq
    @0
    @4
    @5
    simp1
    @0
    @1
    @2
    @3
    @5
    simp22
    @0
    @1
    @2
    @3
    @5
    simp23
    @0
    @1
    @2
    @3
    @5
    simp21
    @0
    @4
    @5
    simp3
    cA
    cS
    cT
    cR
    c.or
    cK
    c.le
    c.an
    cdleme20z.l
    cdleme20z.j
    cdleme20z.m
    cdleme20z.a
    2llnma2rN
    syl131anc
end
