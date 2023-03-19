include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "wa.mm"
include "cneg.mm"
include "caddc.mm"
include "codd.mm"
include "znegcl.mm"
include "adantr.mm"
include "adantl.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wb.mm"
include "peano2zm.mm"
include "zcnd.mm"
include "2cnd.mm"
include "2ne0.mm"
include "a1i.mm"
include "w3a.mm"
include "divneg.mm"
include "eleq1d.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "wceq.mm"
include "zcn.mm"
include "1cnd.mm"
include "negsubdi.mm"
include "eqcomd.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "mpbird.mm"
include "jca.mm"
include "isodd2.mm"
include "isodd.mm"
include "3imtr4i.mm"

theorem onego
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( A e. Odd -> -u A e. Odd )

  proof
    cA
    cz
    wcel
    #
    cA
    c1
    cmin
    co
    #
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
    @5
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    wa
    cA
    codd
    wcel
    @5
    codd
    wcel
    @4
    @6
    @9
    @0
    @6
    @3
    cA
    znegcl
    adantr
    @4
    @9
    @1
    cneg
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    @4
    @2
    cneg
    #
    cz
    wcel
    #
    @12
    @3
    @14
    @0
    @2
    znegcl
    adantl
    @4
    @1
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
    @14
    @12
    wb
    @0
    @15
    @3
    @0
    @1
    cA
    peano2zm
    zcnd
    adantr
    @4
    2cnd
    @17
    @4
    2ne0
    a1i
    @15
    @16
    @17
    w3a
    @13
    @11
    cz
    @1
    c2
    divneg
    eleq1d
    syl3anc
    mpbid
    @0
    @9
    @12
    wb
    @3
    @0
    @8
    @11
    cz
    @0
    @7
    @10
    c2
    cdiv
    @0
    cA
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @7
    @10
    wceq
    cA
    zcn
    @0
    1cnd
    @18
    @19
    wa
    @10
    @7
    cA
    c1
    negsubdi
    eqcomd
    syl2anc
    oveq1d
    eleq1d
    adantr
    mpbird
    jca
    cA
    isodd2
    @5
    isodd
    3imtr4i
end
