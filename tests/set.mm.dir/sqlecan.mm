include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "wb.mm"
include "clt.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "0re.mm"
include "leloe.mm"
include "mpan.mm"
include "w3a.mm"
include "cc.mm"
include "recn.mm"
include "sqval.mm"
include "syl.mm"
include "breq1d.mm"
include "3ad2ant1.mm"
include "lemul1.mm"
include "bitr4d.mm"
include "3exp.mm"
include "exp4a.mm"
include "pm2.43a.mm"
include "adantrd.mm"
include "com23.mm"
include "sq0.mm"
include "0le0.mm"
include "eqbrtri.mm"
include "mul01d.mm"
include "syl5breqr.mm"
include "adantl.mm"
include "oveq1.mm"
include "oveq2.mm"
include "breq12d.mm"
include "adantr.mm"
include "mpbid.mm"
include "adantrr.mm"
include "breq1.mm"
include "biimpa.mm"
include "adantrl.mm"
include "2thd.mm"
include "ex.mm"
include "a1i.mm"
include "jaod.mm"
include "sylbid.mm"
include "imp31.mm"

theorem sqlecan
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ ( B e. RR /\ 0 <_ B ) ) -> ( ( A ^ 2 ) <_ ( B x. A ) <-> A <_ B ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    cB
    cr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    cA
    c2
    cexp
    co
    #
    cB
    cA
    cmul
    co
    #
    cle
    wbr
    #
    cA
    cB
    cle
    wbr
    #
    wb
    #
    @0
    @1
    cc0
    cA
    clt
    wbr
    #
    cc0
    cA
    wceq
    #
    wo
    #
    @4
    @9
    wi
    #
    cc0
    cr
    wcel
    @0
    @1
    @12
    wb
    0re
    cc0
    cA
    leloe
    mpan
    @0
    @10
    @13
    @11
    @0
    @4
    @10
    @9
    @0
    @2
    @10
    @9
    wi
    #
    @3
    @2
    @0
    @14
    @0
    @2
    @0
    @10
    @9
    @0
    @2
    @0
    @10
    wa
    #
    @9
    @0
    @2
    @15
    w3a
    @7
    cA
    cA
    cmul
    co
    #
    @6
    cle
    wbr
    #
    @8
    @0
    @2
    @7
    @17
    wb
    @15
    @0
    @5
    @16
    @6
    cle
    @0
    cA
    cc
    wcel
    @5
    @16
    wceq
    cA
    recn
    cA
    sqval
    syl
    breq1d
    3ad2ant1
    cA
    cB
    cA
    lemul1
    bitr4d
    3exp
    exp4a
    pm2.43a
    adantrd
    com23
    @11
    @13
    wi
    @0
    @11
    @4
    @9
    @11
    @4
    wa
    @7
    @8
    @11
    @2
    @7
    @3
    @11
    @2
    wa
    cc0
    c2
    cexp
    co
    #
    cB
    cc0
    cmul
    co
    #
    cle
    wbr
    #
    @7
    @2
    @20
    @11
    @2
    @18
    cc0
    @19
    cle
    @18
    cc0
    cc0
    cle
    sq0
    0le0
    eqbrtri
    @2
    cB
    cB
    recn
    mul01d
    syl5breqr
    adantl
    @11
    @20
    @7
    wb
    @2
    @11
    @18
    @5
    @19
    @6
    cle
    cc0
    cA
    c2
    cexp
    oveq1
    cc0
    cA
    cB
    cmul
    oveq2
    breq12d
    adantr
    mpbid
    adantrr
    @11
    @3
    @8
    @2
    @11
    @3
    @8
    cc0
    cA
    cB
    cle
    breq1
    biimpa
    adantrl
    2thd
    ex
    a1i
    jaod
    sylbid
    imp31
end
