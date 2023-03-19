include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cbs.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3l.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simp3r.mm"
include "lhple.mm"
include "syl112anc.mm"

theorem lhpat4N
  let cA: class A
  let cP: class P
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume lhpat.l: |- .<_ = ( le ` K )
  assume lhpat.j: |- .\/ = ( join ` K )
  assume lhpat.m: |- ./\ = ( meet ` K )
  assume lhpat.a: |- A = ( Atoms ` K )
  assume lhpat.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( U e. A /\ U .<_ W ) ) -> ( ( P .\/ U ) ./\ W ) = U )

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
    cU
    cA
    wcel
    #
    cU
    cW
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    @0
    @1
    cU
    cK
    cbs
    cfv
    #
    wcel
    #
    @3
    cP
    cU
    c.or
    co
    cW
    c.an
    co
    cU
    wceq
    @0
    @1
    @4
    simp1
    @0
    @1
    @4
    simp2
    @5
    @2
    @7
    @0
    @1
    @2
    @3
    simp3l
    cA
    @6
    cU
    cK
    @6
    eqid
    #
    lhpat.a
    atbase
    syl
    @0
    @1
    @2
    @3
    simp3r
    cA
    @6
    cP
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cU
    @8
    lhpat.l
    lhpat.j
    lhpat.m
    lhpat.a
    lhpat.h
    lhple
    syl112anc
end
