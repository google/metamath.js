include "cal.mm"
include "wcel.mm"
include "w3a.mm"
include "cpo.mm"
include "cbs.mm"
include "cfv.mm"
include "cp0.mm"
include "ccvr.mm"
include "wbr.mm"
include "wceq.mm"
include "wb.mm"
include "atlpos.mm"
include "3ad2ant1.mm"
include "eqid.mm"
include "atbase.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "atl0cl.mm"
include "atcvr0.mm"
include "3adant3.mm"
include "3adant2.mm"
include "cvrcmp.mm"
include "syl132anc.mm"

theorem atcmp
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cK: class K
  let c.le: class .<_
  assume atcmp.l: |- .<_ = ( le ` K )
  assume atcmp.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. AtLat /\ P e. A /\ Q e. A ) -> ( P .<_ Q <-> P = Q ) )

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
    cK
    cpo
    wcel
    #
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    cQ
    @4
    wcel
    #
    cK
    cp0
    cfv
    #
    @4
    wcel
    #
    @7
    cP
    cK
    ccvr
    cfv
    #
    wbr
    #
    @7
    cQ
    @9
    wbr
    #
    cP
    cQ
    c.le
    wbr
    cP
    cQ
    wceq
    wb
    @0
    @1
    @3
    @2
    cK
    atlpos
    3ad2ant1
    @1
    @0
    @5
    @2
    cA
    @4
    cP
    cK
    @4
    eqid
    #
    atcmp.a
    atbase
    3ad2ant2
    @2
    @0
    @6
    @1
    cA
    @4
    cQ
    cK
    @12
    atcmp.a
    atbase
    3ad2ant3
    @0
    @1
    @8
    @2
    @4
    cK
    @7
    @12
    @7
    eqid
    #
    atl0cl
    3ad2ant1
    @0
    @1
    @10
    @2
    cA
    @9
    cal
    cP
    cK
    @7
    @13
    @9
    eqid
    #
    atcmp.a
    atcvr0
    3adant3
    @0
    @2
    @11
    @1
    cA
    @9
    cal
    cQ
    cK
    @7
    @13
    @14
    atcmp.a
    atcvr0
    3adant2
    @4
    @9
    cK
    c.le
    cP
    cQ
    @7
    @12
    atcmp.l
    @14
    cvrcmp
    syl132anc
end
