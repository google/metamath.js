include "cch.mm"
include "wcel.mm"
include "w3a.mm"
include "cdmd.mm"
include "wbr.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "wa.mm"
include "cin.mm"
include "wceq.mm"
include "wi.mm"
include "dmdi.mm"
include "exp32.mm"
include "3com12.mm"
include "imp32.mm"
include "3adantr3.mm"
include "chjcom.mm"
include "ineq2d.mm"
include "3adant3.mm"
include "df-ss.mm"
include "biimpi.mm"
include "sylan9req.mm"
include "3ad2antr3.mm"
include "eqtrd.mm"

theorem dmdsl3
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. CH /\ B e. CH /\ C e. CH ) /\ ( B MH* A /\ A C_ C /\ C C_ ( A vH B ) ) ) -> ( ( C i^i B ) vH A ) = C )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cC
    cch
    wcel
    #
    w3a
    #
    cB
    cA
    cdmd
    wbr
    #
    cA
    cC
    wss
    #
    cC
    cA
    cB
    chj
    co
    #
    wss
    #
    w3a
    wa
    cC
    cB
    cin
    cA
    chj
    co
    #
    cC
    cB
    cA
    chj
    co
    #
    cin
    #
    cC
    @3
    @4
    @5
    @8
    @10
    wceq
    #
    @7
    @3
    @4
    @5
    @11
    @1
    @0
    @2
    @4
    @5
    @11
    wi
    wi
    @1
    @0
    @2
    w3a
    @4
    @5
    @11
    cB
    cA
    cC
    dmdi
    exp32
    3com12
    imp32
    3adantr3
    @3
    @4
    @7
    @10
    cC
    wceq
    @5
    @3
    @7
    @10
    cC
    @6
    cin
    #
    cC
    @0
    @1
    @12
    @10
    wceq
    @2
    @0
    @1
    wa
    @6
    @9
    cC
    cA
    cB
    chjcom
    ineq2d
    3adant3
    @7
    @12
    cC
    wceq
    cC
    @6
    df-ss
    biimpi
    sylan9req
    3ad2antr3
    eqtrd
end
