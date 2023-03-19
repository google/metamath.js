include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "hllat.mm"
include "adantr.mm"
include "simpr1.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simpr2.mm"
include "simpr3.mm"
include "latjass.mm"
include "syl13anc.mm"

theorem hlatjass
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  assume hlatjcom.j: |- .\/ = ( join ` K )
  assume hlatjcom.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) ) -> ( ( P .\/ Q ) .\/ R ) = ( P .\/ ( Q .\/ R ) ) )

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
    wa
    #
    cK
    clat
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
    @7
    wcel
    #
    cR
    @7
    wcel
    #
    cP
    cQ
    c.or
    co
    cR
    c.or
    co
    cP
    cQ
    cR
    c.or
    co
    c.or
    co
    wceq
    @0
    @6
    @4
    cK
    hllat
    adantr
    @5
    @1
    @8
    @0
    @1
    @2
    @3
    simpr1
    cA
    @7
    cP
    cK
    @7
    eqid
    #
    hlatjcom.a
    atbase
    syl
    @5
    @2
    @9
    @0
    @1
    @2
    @3
    simpr2
    cA
    @7
    cQ
    cK
    @11
    hlatjcom.a
    atbase
    syl
    @5
    @3
    @10
    @0
    @1
    @2
    @3
    simpr3
    cA
    @7
    cR
    cK
    @11
    hlatjcom.a
    atbase
    syl
    @7
    c.or
    cK
    cP
    cQ
    cR
    @11
    hlatjcom.j
    latjass
    syl13anc
end
