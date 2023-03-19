include "cpr.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "wn.mm"
include "neneq.mm"
include "adantl.mm"
include "wo.mm"
include "elpri.mm"
include "adantr.mm"
include "ord.mm"
include "mpd.mm"

theorem elprn1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. { B , C } /\ A =/= B ) -> A = C )

  proof
    cA
    cB
    cC
    cpr
    wcel
    #
    cA
    cB
    wne
    #
    wa
    #
    cA
    cB
    wceq
    #
    wn
    #
    cA
    cC
    wceq
    #
    @1
    @4
    @0
    cA
    cB
    neneq
    adantl
    @2
    @3
    @5
    @0
    @3
    @5
    wo
    @1
    cA
    cB
    cC
    elpri
    adantr
    ord
    mpd
end
