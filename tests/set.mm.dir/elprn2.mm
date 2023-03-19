include "cpr.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "wn.mm"
include "neneq.mm"
include "adantl.mm"
include "wo.mm"
include "wi.mm"
include "elpri.mm"
include "adantr.mm"
include "orcom.mm"
include "df-or.mm"
include "bitri.mm"
include "sylib.mm"
include "mpd.mm"

theorem elprn2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. { B , C } /\ A =/= C ) -> A = B )

  proof
    cA
    cB
    cC
    cpr
    wcel
    #
    cA
    cC
    wne
    #
    wa
    #
    cA
    cC
    wceq
    #
    wn
    #
    cA
    cB
    wceq
    #
    @1
    @4
    @0
    cA
    cC
    neneq
    adantl
    @2
    @5
    @3
    wo
    #
    @4
    @5
    wi
    #
    @0
    @6
    @1
    cA
    cB
    cC
    elpri
    adantr
    @6
    @3
    @5
    wo
    @7
    @5
    @3
    orcom
    @3
    @5
    df-or
    bitri
    sylib
    mpd
end
