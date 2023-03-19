include "cprime.mm"
include "wcel.mm"
include "ceven.mm"
include "c2.mm"
include "wceq.mm"
include "wi.mm"
include "2a1.mm"
include "wn.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "codd.mm"
include "wne.mm"
include "df-ne.mm"
include "biimpri.mm"
include "anim2i.mm"
include "ancoms.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "oddprmALTV.mm"
include "oddneven.mm"
include "pm2.21d.mm"
include "3syl.mm"
include "ex.mm"
include "pm2.61i.mm"
include "2evenALTV.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "impbid1.mm"

theorem evenprm2
  let cP: class P
  let vk: setvar k
  let vx: setvar x


  assert |- ( P e. Prime -> ( P e. Even <-> P = 2 ) )

  proof
    cP
    cprime
    wcel
    #
    cP
    ceven
    wcel
    #
    cP
    c2
    wceq
    #
    @2
    @0
    @1
    @2
    wi
    #
    wi
    @2
    @0
    @1
    2a1
    @2
    wn
    #
    @0
    @3
    @4
    @0
    wa
    #
    cP
    cprime
    c2
    csn
    cdif
    wcel
    #
    cP
    codd
    wcel
    #
    @3
    @5
    @0
    cP
    c2
    wne
    #
    wa
    #
    @6
    @0
    @4
    @9
    @4
    @8
    @0
    @8
    @4
    cP
    c2
    df-ne
    biimpri
    anim2i
    ancoms
    cP
    cprime
    c2
    eldifsn
    sylibr
    cP
    oddprmALTV
    @7
    @1
    @2
    cP
    oddneven
    pm2.21d
    3syl
    ex
    pm2.61i
    @2
    @1
    c2
    ceven
    wcel
    2evenALTV
    cP
    c2
    ceven
    eleq1
    mpbiri
    impbid1
end
