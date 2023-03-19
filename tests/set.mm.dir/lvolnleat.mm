include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wa.mm"
include "wn.mm"
include "3simpa.mm"
include "simp3.mm"
include "eqid.mm"
include "lvolnle3at.mm"
include "syl13anc.mm"
include "wceq.mm"
include "hlatjidm.mm"
include "3adant2.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "mtbid.mm"

theorem lvolnleat
  let cA: class A
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cX: class X
  assume lvolnleat.l: |- .<_ = ( le ` K )
  assume lvolnleat.a: |- A = ( Atoms ` K )
  assume lvolnleat.v: |- V = ( LVols ` K )


  assert |- ( ( K e. HL /\ X e. V /\ P e. A ) -> -. X .<_ P )

  proof
    cK
    chlt
    wcel
    #
    cX
    cV
    wcel
    #
    cP
    cA
    wcel
    #
    w3a
    #
    cX
    cP
    cP
    cK
    cjn
    cfv
    #
    co
    #
    cP
    @4
    co
    #
    c.le
    wbr
    #
    cX
    cP
    c.le
    wbr
    @3
    @0
    @1
    wa
    @2
    @2
    @2
    @7
    wn
    @0
    @1
    @2
    3simpa
    @0
    @1
    @2
    simp3
    #
    @8
    @8
    cA
    cP
    cP
    cP
    @4
    cK
    c.le
    cV
    cX
    lvolnleat.l
    @4
    eqid
    #
    lvolnleat.a
    lvolnleat.v
    lvolnle3at
    syl13anc
    @3
    @6
    cP
    cX
    c.le
    @3
    @6
    @5
    cP
    @3
    @5
    cP
    cP
    @4
    @0
    @2
    @5
    cP
    wceq
    @1
    cA
    @4
    cK
    cP
    @9
    lvolnleat.a
    hlatjidm
    3adant2
    #
    oveq1d
    @10
    eqtrd
    breq2d
    mtbid
end
