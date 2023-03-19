include "con0.mm"
include "wcel.mm"
include "w3a.mm"
include "c0.mm"
include "wss.mm"
include "coe.mm"
include "co.mm"
include "wi.mm"
include "c1o.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "word.mm"
include "eloni.mm"
include "ordgt0ge1.mm"
include "syl.mm"
include "1on.mm"
include "onsseleq.mm"
include "mpan.mm"
include "bitrd.mm"
include "3ad2ant3.mm"
include "wa.mm"
include "c2o.mm"
include "cdif.mm"
include "ondif2.mm"
include "oeword.mm"
include "biimpd.mm"
include "3expia.mm"
include "syl5bir.mm"
include "expd.mm"
include "3impia.mm"
include "oe1m.mm"
include "adantr.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "eqimss.mm"
include "oveq1.mm"
include "sseq12d.mm"
include "syl5ibcom.mm"
include "3adant3.mm"
include "a1dd.mm"
include "jaod.mm"
include "sylbid.mm"
include "imp.mm"

theorem oewordi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. On /\ B e. On /\ C e. On ) /\ (/) e. C ) -> ( A C_ B -> ( C ^o A ) C_ ( C ^o B ) ) )

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
    coe
    co
    #
    cC
    cB
    coe
    co
    #
    wss
    #
    wi
    #
    @3
    @4
    c1o
    cC
    wcel
    #
    c1o
    cC
    wceq
    #
    wo
    #
    @9
    @2
    @0
    @4
    @12
    wb
    @1
    @2
    @4
    c1o
    cC
    wss
    #
    @12
    @2
    cC
    word
    @4
    @13
    wb
    cC
    eloni
    cC
    ordgt0ge1
    syl
    c1o
    con0
    wcel
    @2
    @13
    @12
    wb
    1on
    c1o
    cC
    onsseleq
    mpan
    bitrd
    3ad2ant3
    @3
    @10
    @9
    @11
    @0
    @1
    @2
    @10
    @9
    wi
    @0
    @1
    wa
    #
    @2
    @10
    @9
    @2
    @10
    wa
    cC
    con0
    c2o
    cdif
    wcel
    #
    @14
    @9
    cC
    ondif2
    @0
    @1
    @15
    @9
    @0
    @1
    @15
    w3a
    @5
    @8
    cA
    cB
    cC
    oeword
    biimpd
    3expia
    syl5bir
    expd
    3impia
    @3
    @11
    @8
    @5
    @0
    @1
    @11
    @8
    wi
    @2
    @14
    c1o
    cA
    coe
    co
    #
    c1o
    cB
    coe
    co
    #
    wss
    #
    @11
    @8
    @14
    @16
    @17
    wceq
    @18
    @14
    @16
    c1o
    @17
    @0
    @16
    c1o
    wceq
    @1
    cA
    oe1m
    adantr
    @1
    @17
    c1o
    wceq
    @0
    cB
    oe1m
    adantl
    eqtr4d
    @16
    @17
    eqimss
    syl
    @11
    @16
    @6
    @17
    @7
    c1o
    cC
    cA
    coe
    oveq1
    c1o
    cC
    cB
    coe
    oveq1
    sseq12d
    syl5ibcom
    3adant3
    a1dd
    jaod
    sylbid
    imp
end
