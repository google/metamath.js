include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "coa.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "wne.mm"
include "wb.mm"
include "on0eln0.mm"
include "adantr.mm"
include "oaword1.mm"
include "sseld.mm"
include "sylbird.mm"
include "ne0i.mm"
include "syl6.mm"
include "necon4d.mm"
include "adantl.mm"
include "0elon.mm"
include "oaord.mm"
include "mp3an1.mm"
include "ancoms.mm"
include "bitr3d.mm"
include "syl6bi.mm"
include "jcad.mm"
include "oveq12.mm"
include "oa0.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "impbid1.mm"

theorem oa00
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( ( A +o B ) = (/) <-> ( A = (/) /\ B = (/) ) ) )

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
    cA
    cB
    coa
    co
    #
    c0
    wceq
    #
    cA
    c0
    wceq
    #
    cB
    c0
    wceq
    #
    wa
    #
    @2
    @4
    @5
    @6
    @2
    cA
    c0
    @3
    c0
    @2
    cA
    c0
    wne
    #
    c0
    @3
    wcel
    #
    @3
    c0
    wne
    #
    @2
    @8
    c0
    cA
    wcel
    #
    @9
    @0
    @11
    @8
    wb
    @1
    cA
    on0eln0
    adantr
    @2
    cA
    @3
    c0
    cA
    cB
    oaword1
    sseld
    sylbird
    @3
    c0
    ne0i
    syl6
    necon4d
    @2
    cB
    c0
    @3
    c0
    @2
    cB
    c0
    wne
    #
    cA
    c0
    coa
    co
    #
    @3
    wcel
    #
    @10
    @2
    c0
    cB
    wcel
    #
    @12
    @14
    @1
    @15
    @12
    wb
    @0
    cB
    on0eln0
    adantl
    @1
    @0
    @15
    @14
    wb
    #
    c0
    con0
    wcel
    #
    @1
    @0
    @16
    0elon
    c0
    cB
    cA
    oaord
    mp3an1
    ancoms
    bitr3d
    @3
    @13
    ne0i
    syl6bi
    necon4d
    jcad
    @7
    @3
    c0
    c0
    coa
    co
    #
    c0
    cA
    c0
    cB
    c0
    coa
    oveq12
    @17
    @18
    c0
    wceq
    0elon
    c0
    oa0
    ax-mp
    syl6eq
    impbid1
end
