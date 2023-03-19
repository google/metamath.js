include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cbs.mm"
include "cfv.mm"
include "ccvr.mm"
include "co.mm"
include "wceq.mm"
include "simpll.mm"
include "eqid.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "lhp1cvr.mm"
include "adantr.mm"
include "simprr.mm"
include "1cvrjat.mm"
include "syl32anc.mm"

theorem lhpjat1
  let cA: class A
  let cP: class P
  let c.1: class .1.
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume lhpjat.l: |- .<_ = ( le ` K )
  assume lhpjat.j: |- .\/ = ( join ` K )
  assume lhpjat.u: |- .1. = ( 1. ` K )
  assume lhpjat.a: |- A = ( Atoms ` K )
  assume lhpjat.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( W .\/ P ) = .1. )

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
    wa
    @0
    cW
    cK
    cbs
    cfv
    #
    wcel
    #
    @3
    cW
    c.1
    cK
    ccvr
    cfv
    #
    wbr
    #
    @4
    cW
    cP
    c.or
    co
    c.1
    wceq
    @0
    @1
    @5
    simpll
    @1
    @7
    @0
    @5
    @6
    cH
    cK
    cW
    @6
    eqid
    #
    lhpjat.h
    lhpbase
    ad2antlr
    @2
    @3
    @4
    simprl
    @2
    @9
    @5
    chlt
    @8
    c.1
    cH
    cK
    cW
    lhpjat.u
    @8
    eqid
    #
    lhpjat.h
    lhp1cvr
    adantr
    @2
    @3
    @4
    simprr
    cA
    @6
    @8
    cP
    c.1
    c.or
    cK
    c.le
    cW
    @10
    lhpjat.l
    lhpjat.j
    lhpjat.u
    @11
    lhpjat.a
    1cvrjat
    syl32anc
end
