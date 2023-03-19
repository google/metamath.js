include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "c1o.mm"
include "comu.mm"
include "co.mm"
include "wceq.mm"
include "om1r.mm"
include "ad2antrr.mm"
include "wss.mm"
include "word.mm"
include "eloni.mm"
include "ordgt0ge1.mm"
include "biimpa.mm"
include "sylan.mm"
include "adantll.mm"
include "wi.mm"
include "1on.mm"
include "omwordri.mm"
include "mp3an1.mm"
include "ancoms.mm"
include "adantr.mm"
include "mpd.mm"
include "eqsstr3d.mm"

theorem omword2
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. On /\ B e. On ) /\ (/) e. B ) -> A C_ ( B .o A ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    c0
    cB
    wcel
    #
    wa
    #
    cA
    c1o
    cA
    comu
    co
    #
    cB
    cA
    comu
    co
    #
    @0
    @5
    cA
    wceq
    @1
    @3
    cA
    om1r
    ad2antrr
    @4
    c1o
    cB
    wss
    #
    @5
    @6
    wss
    #
    @1
    @3
    @7
    @0
    @1
    cB
    word
    #
    @3
    @7
    cB
    eloni
    @9
    @3
    @7
    cB
    ordgt0ge1
    biimpa
    sylan
    adantll
    @2
    @7
    @8
    wi
    #
    @3
    @1
    @0
    @10
    c1o
    con0
    wcel
    @1
    @0
    @10
    1on
    c1o
    cB
    cA
    omwordri
    mp3an1
    ancoms
    adantr
    mpd
    eqsstr3d
end
