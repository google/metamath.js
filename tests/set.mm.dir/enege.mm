include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "wa.mm"
include "cneg.mm"
include "ceven.mm"
include "znegcl.mm"
include "adantr.mm"
include "adantl.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "wb.mm"
include "zcn.mm"
include "2cnd.mm"
include "2ne0.mm"
include "a1i.mm"
include "3jca.mm"
include "divneg.mm"
include "eleq1d.mm"
include "syl.mm"
include "mpbid.mm"
include "jca.mm"
include "iseven.mm"
include "3imtr4i.mm"

theorem enege
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( A e. Even -> -u A e. Even )

  proof
    cA
    cz
    wcel
    #
    cA
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    wa
    #
    cA
    cneg
    #
    cz
    wcel
    #
    @4
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    wa
    cA
    ceven
    wcel
    @4
    ceven
    wcel
    @3
    @5
    @7
    @0
    @5
    @2
    cA
    znegcl
    adantr
    @3
    @1
    cneg
    #
    cz
    wcel
    #
    @7
    @2
    @9
    @0
    @1
    znegcl
    adantl
    @3
    cA
    cc
    wcel
    #
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    w3a
    #
    @9
    @7
    wb
    @0
    @13
    @2
    @0
    @10
    @11
    @12
    cA
    zcn
    @0
    2cnd
    @12
    @0
    2ne0
    a1i
    3jca
    adantr
    @13
    @8
    @6
    cz
    cA
    c2
    divneg
    eleq1d
    syl
    mpbid
    jca
    cA
    iseven
    @4
    iseven
    3imtr4i
end
