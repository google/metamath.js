include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "wa.mm"
include "oveq1.mm"
include "hlatjidm.mm"
include "3adant2.mm"
include "sylan9eqr.mm"
include "llnneat.mm"
include "adantlr.mm"
include "ex.mm"
include "con2d.mm"
include "3impia.mm"
include "adantr.mm"
include "eqneltrd.mm"
include "necon2ad.mm"
include "llni2.mm"
include "impbid.mm"

theorem islln2a
  let cA: class A
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let cN: class N
  assume islln2a.j: |- .\/ = ( join ` K )
  assume islln2a.a: |- A = ( Atoms ` K )
  assume islln2a.n: |- N = ( LLines ` K )


  assert |- ( ( K e. HL /\ P e. A /\ Q e. A ) -> ( ( P .\/ Q ) e. N <-> P =/= Q ) )

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
    w3a
    #
    cP
    cQ
    c.or
    co
    #
    cN
    wcel
    #
    cP
    cQ
    wne
    #
    @3
    @5
    cP
    cQ
    @3
    cP
    cQ
    wceq
    #
    @5
    wn
    @3
    @7
    wa
    @4
    cQ
    cN
    @7
    @3
    @4
    cQ
    cQ
    c.or
    co
    #
    cQ
    cP
    cQ
    cQ
    c.or
    oveq1
    @0
    @2
    @8
    cQ
    wceq
    @1
    cA
    c.or
    cK
    cQ
    islln2a.j
    islln2a.a
    hlatjidm
    3adant2
    sylan9eqr
    @3
    cQ
    cN
    wcel
    #
    wn
    #
    @7
    @0
    @1
    @2
    @10
    @0
    @1
    wa
    #
    @9
    @2
    @11
    @9
    @2
    wn
    #
    @0
    @9
    @12
    @1
    cA
    cK
    cN
    cQ
    islln2a.a
    islln2a.n
    llnneat
    adantlr
    ex
    con2d
    3impia
    adantr
    eqneltrd
    ex
    necon2ad
    @3
    @6
    @5
    cA
    cP
    cQ
    c.or
    cK
    cN
    islln2a.j
    islln2a.a
    islln2a.n
    llni2
    ex
    impbid
end
