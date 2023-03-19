include "cal.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cp0.mm"
include "cfv.mm"
include "wne.mm"
include "eqid.mm"
include "atn0.mm"
include "3adant3.mm"
include "cbs.mm"
include "wceq.mm"
include "wb.mm"
include "atbase.mm"
include "cple.mm"
include "atcvreq0.mm"
include "syl3an2.mm"
include "necon3bbid.mm"
include "mpbird.mm"

theorem atncvrN
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cK: class K
  assume atncvr.c: |- C = ( <o ` K )
  assume atncvr.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. AtLat /\ P e. A /\ Q e. A ) -> -. P C Q )

  proof
    cK
    cal
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
    w3a
    #
    cP
    cQ
    cC
    wbr
    #
    wn
    cP
    cK
    cp0
    cfv
    #
    wne
    #
    @0
    @1
    @6
    @2
    cA
    cP
    cK
    @5
    @5
    eqid
    #
    atncvr.a
    atn0
    3adant3
    @3
    @4
    cP
    @5
    @1
    @0
    cP
    cK
    cbs
    cfv
    #
    wcel
    @2
    @4
    cP
    @5
    wceq
    wb
    cA
    @8
    cP
    cK
    @8
    eqid
    #
    atncvr.a
    atbase
    cA
    @8
    cC
    cQ
    cK
    cK
    cple
    cfv
    #
    cP
    @5
    @9
    @10
    eqid
    @7
    atncvr.c
    atncvr.a
    atcvreq0
    syl3an2
    necon3bbid
    mpbird
end
