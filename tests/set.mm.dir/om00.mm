include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "comu.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "c1o.mm"
include "wss.mm"
include "wne.mm"
include "neanior.mm"
include "wi.mm"
include "word.mm"
include "wb.mm"
include "eloni.mm"
include "ordge1n0.mm"
include "syl.mm"
include "biimprd.mm"
include "adantr.mm"
include "on0eln0.mm"
include "adantl.mm"
include "omword1.mm"
include "ex.mm"
include "sylbird.mm"
include "anim12d.mm"
include "sstr.mm"
include "syl6.mm"
include "syl5bir.mm"
include "omcl.mm"
include "3syl.mm"
include "sylibd.mm"
include "necon4bd.mm"
include "oveq1.mm"
include "om0r.mm"
include "sylan9eqr.mm"
include "oveq2.mm"
include "om0.mm"
include "jaod.mm"
include "impbid.mm"

theorem om00
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( ( A .o B ) = (/) <-> ( A = (/) \/ B = (/) ) ) )

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
    comu
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
    wo
    #
    @2
    @7
    @3
    c0
    @2
    @7
    wn
    #
    c1o
    @3
    wss
    #
    @3
    c0
    wne
    #
    @8
    cA
    c0
    wne
    #
    cB
    c0
    wne
    #
    wa
    #
    @2
    @9
    cA
    c0
    cB
    c0
    neanior
    @2
    @13
    c1o
    cA
    wss
    #
    cA
    @3
    wss
    #
    wa
    @9
    @2
    @11
    @14
    @12
    @15
    @0
    @11
    @14
    wi
    @1
    @0
    @14
    @11
    @0
    cA
    word
    @14
    @11
    wb
    cA
    eloni
    cA
    ordge1n0
    syl
    biimprd
    adantr
    @2
    @12
    c0
    cB
    wcel
    #
    @15
    @1
    @16
    @12
    wb
    @0
    cB
    on0eln0
    adantl
    @2
    @16
    @15
    cA
    cB
    omword1
    ex
    sylbird
    anim12d
    c1o
    cA
    @3
    sstr
    syl6
    syl5bir
    @2
    @3
    con0
    wcel
    @3
    word
    @9
    @10
    wb
    cA
    cB
    omcl
    @3
    eloni
    @3
    ordge1n0
    3syl
    sylibd
    necon4bd
    @2
    @5
    @4
    @6
    @1
    @5
    @4
    wi
    @0
    @1
    @5
    @4
    @5
    @1
    @3
    c0
    cB
    comu
    co
    c0
    cA
    c0
    cB
    comu
    oveq1
    cB
    om0r
    sylan9eqr
    ex
    adantl
    @0
    @6
    @4
    wi
    @1
    @0
    @6
    @4
    @6
    @0
    @3
    cA
    c0
    comu
    co
    c0
    cB
    c0
    cA
    comu
    oveq2
    cA
    om0
    sylan9eqr
    ex
    adantr
    jaod
    impbid
end
