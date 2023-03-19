include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "wi.mm"
include "clt.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "0re.mm"
include "leloe.mm"
include "mpan.mm"
include "pm5.32i.mm"
include "lemul1.mm"
include "biimpd.mm"
include "3expia.mm"
include "com12.mm"
include "leidi.mm"
include "recn.mm"
include "mul01d.mm"
include "breqan12d.mm"
include "mpbiri.mm"
include "oveq2.mm"
include "breq12d.mm"
include "syl5ib.mm"
include "a1dd.mm"
include "adantl.mm"
include "jaodan.mm"
include "sylbi.mm"
include "3impia.mm"
include "imp.mm"

theorem lemul1a
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR /\ B e. RR /\ ( C e. RR /\ 0 <_ C ) ) /\ A <_ B ) -> ( A x. C ) <_ ( B x. C ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    cc0
    cC
    cle
    wbr
    #
    wa
    #
    w3a
    cA
    cB
    cle
    wbr
    #
    cA
    cC
    cmul
    co
    #
    cB
    cC
    cmul
    co
    #
    cle
    wbr
    #
    @0
    @1
    @4
    @5
    @8
    wi
    #
    @4
    @0
    @1
    wa
    #
    @9
    @4
    @2
    cc0
    cC
    clt
    wbr
    #
    cc0
    cC
    wceq
    #
    wo
    #
    wa
    @10
    @9
    wi
    #
    @2
    @3
    @13
    cc0
    cr
    wcel
    @2
    @3
    @13
    wb
    0re
    cc0
    cC
    leloe
    mpan
    pm5.32i
    @2
    @11
    @14
    @12
    @10
    @2
    @11
    wa
    #
    @9
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
    lemul1
    biimpd
    3expia
    com12
    @12
    @14
    @2
    @12
    @10
    @8
    @5
    @10
    cA
    cc0
    cmul
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
    @12
    @8
    @10
    @18
    cc0
    cc0
    cle
    wbr
    cc0
    0re
    leidi
    @0
    @1
    @16
    cc0
    @17
    cc0
    cle
    @0
    cA
    cA
    recn
    mul01d
    @1
    cB
    cB
    recn
    mul01d
    breqan12d
    mpbiri
    @12
    @16
    @6
    @17
    @7
    cle
    cc0
    cC
    cA
    cmul
    oveq2
    cc0
    cC
    cB
    cmul
    oveq2
    breq12d
    syl5ib
    a1dd
    adantl
    jaodan
    sylbi
    com12
    3impia
    imp
end
