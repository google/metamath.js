include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "cp0.mm"
include "cfv.mm"
include "wne.mm"
include "cal.mm"
include "hlatl.mm"
include "3ad2ant1.mm"
include "simp21.mm"
include "eqid.mm"
include "atn0.mm"
include "syl2anc.mm"
include "cbs.mm"
include "wceq.mm"
include "wb.mm"
include "simp1.mm"
include "atbase.mm"
include "syl.mm"
include "simp22.mm"
include "simp23.mm"
include "simp3.mm"
include "atcvrj0.mm"
include "syl131anc.mm"
include "necon3bid.mm"
include "mpbid.mm"

theorem atcvrneN
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  assume atcvrne.j: |- .\/ = ( join ` K )
  assume atcvrne.c: |- C = ( <o ` K )
  assume atcvrne.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ P C ( Q .\/ R ) ) -> Q =/= R )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    cR
    cA
    wcel
    #
    w3a
    #
    cP
    cQ
    cR
    c.or
    co
    cC
    wbr
    #
    w3a
    #
    cP
    cK
    cp0
    cfv
    #
    wne
    #
    cQ
    cR
    wne
    @6
    cK
    cal
    wcel
    #
    @1
    @8
    @0
    @4
    @9
    @5
    cK
    hlatl
    3ad2ant1
    @0
    @1
    @2
    @3
    @5
    simp21
    #
    cA
    cP
    cK
    @7
    @7
    eqid
    #
    atcvrne.a
    atn0
    syl2anc
    @6
    cP
    @7
    cQ
    cR
    @6
    @0
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    @2
    @3
    @5
    cP
    @7
    wceq
    cQ
    cR
    wceq
    wb
    @0
    @4
    @5
    simp1
    @6
    @1
    @13
    @10
    cA
    @12
    cP
    cK
    @12
    eqid
    #
    atcvrne.a
    atbase
    syl
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
    @4
    @5
    simp3
    cA
    @12
    cC
    cQ
    cR
    c.or
    cK
    cP
    @7
    @14
    atcvrne.j
    @11
    atcvrne.c
    atcvrne.a
    atcvrj0
    syl131anc
    necon3bid
    mpbid
end
