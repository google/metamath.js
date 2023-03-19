include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wa.mm"
include "cp0.mm"
include "cfv.mm"
include "wne.mm"
include "cal.mm"
include "hlatl.mm"
include "3ad2ant1.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "atn0.mm"
include "sylancom.mm"
include "ex.mm"
include "wceq.mm"
include "clat.mm"
include "simpll1.mm"
include "hllat.mm"
include "syl.mm"
include "simpll2.mm"
include "simpll3.mm"
include "latmcom.mm"
include "syl3anc.mm"
include "simplr.mm"
include "wb.mm"
include "simpr.mm"
include "atnle.mm"
include "mpbid.mm"
include "eqtrd.mm"
include "necon3ad.mm"
include "syld.mm"
include "impr.mm"

theorem intnatN
  let cA: class A
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  assume intnat.b: |- B = ( Base ` K )
  assume intnat.l: |- .<_ = ( le ` K )
  assume intnat.m: |- ./\ = ( meet ` K )
  assume intnat.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ X e. B /\ Y e. B ) /\ ( -. Y .<_ X /\ ( X ./\ Y ) e. A ) ) -> -. Y e. A )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cY
    cX
    c.le
    wbr
    wn
    #
    cX
    cY
    c.an
    co
    #
    cA
    wcel
    #
    cY
    cA
    wcel
    #
    wn
    #
    @3
    @4
    wa
    #
    @6
    @5
    cK
    cp0
    cfv
    #
    wne
    #
    @8
    @9
    @6
    @11
    @9
    @6
    cK
    cal
    wcel
    #
    @11
    @3
    @12
    @4
    @6
    @0
    @1
    @12
    @2
    cK
    hlatl
    #
    3ad2ant1
    ad2antrr
    cA
    @5
    cK
    @10
    @10
    eqid
    #
    intnat.a
    atn0
    sylancom
    ex
    @9
    @7
    @5
    @10
    @9
    @7
    @5
    @10
    wceq
    @9
    @7
    wa
    #
    @5
    cY
    cX
    c.an
    co
    #
    @10
    @15
    cK
    clat
    wcel
    #
    @1
    @2
    @5
    @16
    wceq
    @15
    @0
    @17
    @0
    @1
    @2
    @4
    @7
    simpll1
    #
    cK
    hllat
    syl
    @0
    @1
    @2
    @4
    @7
    simpll2
    #
    @0
    @1
    @2
    @4
    @7
    simpll3
    cB
    cK
    c.an
    cX
    cY
    intnat.b
    intnat.m
    latmcom
    syl3anc
    @15
    @4
    @16
    @10
    wceq
    #
    @3
    @4
    @7
    simplr
    @15
    @12
    @7
    @1
    @4
    @20
    wb
    @15
    @0
    @12
    @18
    @13
    syl
    @9
    @7
    simpr
    @19
    cA
    cB
    cY
    cK
    c.le
    c.an
    cX
    @10
    intnat.b
    intnat.l
    intnat.m
    @14
    intnat.a
    atnle
    syl3anc
    mpbid
    eqtrd
    ex
    necon3ad
    syld
    impr
end
