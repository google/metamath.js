include "con0.mm"
include "wcel.mm"
include "w3a.mm"
include "c0.mm"
include "wa.mm"
include "comu.mm"
include "co.mm"
include "wb.mm"
include "omord2.mm"
include "ex.mm"
include "pm5.32rd.mm"
include "simpl.mm"
include "wi.mm"
include "wne.mm"
include "ne0i.mm"
include "wceq.mm"
include "om0r.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "necon3d.mm"
include "syl5.mm"
include "adantr.mm"
include "on0eln0.mm"
include "adantl.mm"
include "sylibrd.mm"
include "3adant1.mm"
include "ancld.mm"
include "impbid2.mm"
include "bitrd.mm"

theorem omord
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. On /\ B e. On /\ C e. On ) -> ( ( A e. B /\ (/) e. C ) <-> ( C .o A ) e. ( C .o B ) ) )

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
    cA
    cB
    wcel
    #
    c0
    cC
    wcel
    #
    wa
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
    wcel
    #
    @5
    wa
    #
    @8
    @3
    @5
    @4
    @8
    @3
    @5
    @4
    @8
    wb
    cA
    cB
    cC
    omord2
    ex
    pm5.32rd
    @3
    @9
    @8
    @8
    @5
    simpl
    @3
    @8
    @5
    @1
    @2
    @8
    @5
    wi
    @0
    @1
    @2
    wa
    @8
    cC
    c0
    wne
    #
    @5
    @1
    @8
    @10
    wi
    @2
    @8
    @7
    c0
    wne
    @1
    @10
    @7
    @6
    ne0i
    @1
    cC
    c0
    @7
    c0
    @1
    @7
    c0
    wceq
    cC
    c0
    wceq
    #
    c0
    cB
    comu
    co
    #
    c0
    wceq
    cB
    om0r
    @11
    @7
    @12
    c0
    cC
    c0
    cB
    comu
    oveq1
    eqeq1d
    syl5ibrcom
    necon3d
    syl5
    adantr
    @2
    @5
    @10
    wb
    @1
    cC
    on0eln0
    adantl
    sylibrd
    3adant1
    ancld
    impbid2
    bitrd
end
