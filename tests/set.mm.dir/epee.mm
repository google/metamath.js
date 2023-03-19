include "ceven.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "codd.mm"
include "evenp1odd.mm"
include "evenm1odd.mm"
include "opoeALTV.mm"
include "syl2an.mm"
include "cc.mm"
include "wb.mm"
include "evenz.mm"
include "zcnd.mm"
include "adantr.mm"
include "1cnd.mm"
include "adantl.mm"
include "w3a.mm"
include "ppncan.mm"
include "eleq1d.mm"
include "syl3anc.mm"
include "mpbid.mm"

theorem epee
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. Even /\ B e. Even ) -> ( A + B ) e. Even )

  proof
    cA
    ceven
    wcel
    #
    cB
    ceven
    wcel
    #
    wa
    #
    cA
    c1
    caddc
    co
    #
    cB
    c1
    cmin
    co
    #
    caddc
    co
    #
    ceven
    wcel
    #
    cA
    cB
    caddc
    co
    #
    ceven
    wcel
    #
    @0
    @3
    codd
    wcel
    @4
    codd
    wcel
    @6
    @1
    cA
    evenp1odd
    cB
    evenm1odd
    @3
    @4
    opoeALTV
    syl2an
    @2
    cA
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @6
    @8
    wb
    @0
    @9
    @1
    @0
    cA
    cA
    evenz
    zcnd
    adantr
    @2
    1cnd
    @1
    @11
    @0
    @1
    cB
    cB
    evenz
    zcnd
    adantl
    @9
    @10
    @11
    w3a
    @5
    @7
    ceven
    cA
    c1
    cB
    ppncan
    eleq1d
    syl3anc
    mpbid
end
