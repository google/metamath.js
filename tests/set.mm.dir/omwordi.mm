include "con0.mm"
include "wcel.mm"
include "w3a.mm"
include "c0.mm"
include "wss.mm"
include "comu.mm"
include "co.mm"
include "wi.mm"
include "wa.mm"
include "omword.mm"
include "biimpd.mm"
include "ex.mm"
include "wn.mm"
include "wceq.mm"
include "wb.mm"
include "word.mm"
include "eloni.mm"
include "ord0eln0.mm"
include "necon2bbid.mm"
include "syl.mm"
include "3ad2ant3.mm"
include "ssid.mm"
include "om0r.mm"
include "adantr.mm"
include "adantl.mm"
include "sseq12d.mm"
include "mpbiri.mm"
include "oveq1.mm"
include "syl5ibrcom.mm"
include "3adant3.mm"
include "sylbird.mm"
include "a1dd.mm"
include "pm2.61d.mm"

theorem omwordi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. On /\ B e. On /\ C e. On ) -> ( A C_ B -> ( C .o A ) C_ ( C .o B ) ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    cC
    con0
    wcel
    #
    w3a
    #
    c0
    cC
    wcel
    #
    cA
    cB
    wss
    #
    cC
    cA
    comu
    co
    #
    cC
    cB
    comu
    co
    #
    wss
    #
    wi
    #
    @3
    @4
    @9
    @3
    @4
    wa
    @5
    @8
    cA
    cB
    cC
    omword
    biimpd
    ex
    @3
    @4
    wn
    #
    @8
    @5
    @3
    @10
    cC
    c0
    wceq
    #
    @8
    @2
    @0
    @11
    @10
    wb
    #
    @1
    @2
    cC
    word
    #
    @12
    cC
    eloni
    @13
    @4
    cC
    c0
    cC
    ord0eln0
    necon2bbid
    syl
    3ad2ant3
    @0
    @1
    @11
    @8
    wi
    @2
    @0
    @1
    wa
    #
    @8
    @11
    c0
    cA
    comu
    co
    #
    c0
    cB
    comu
    co
    #
    wss
    #
    @14
    @17
    c0
    c0
    wss
    c0
    ssid
    @14
    @15
    c0
    @16
    c0
    @0
    @15
    c0
    wceq
    @1
    cA
    om0r
    adantr
    @1
    @16
    c0
    wceq
    @0
    cB
    om0r
    adantl
    sseq12d
    mpbiri
    @11
    @6
    @15
    @7
    @16
    cC
    c0
    cA
    comu
    oveq1
    cC
    c0
    cB
    comu
    oveq1
    sseq12d
    syl5ibrcom
    3adant3
    sylbird
    a1dd
    pm2.61d
end
