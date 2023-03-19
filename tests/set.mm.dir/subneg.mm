include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "caddc.mm"
include "df-neg.mm"
include "oveq2i.mm"
include "wceq.mm"
include "0cn.mm"
include "subsub.mm"
include "mp3an2.mm"
include "syl5eq.mm"
include "subid1.mm"
include "adantr.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem subneg
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( A - -u B ) = ( A + B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cB
    cneg
    #
    cmin
    co
    #
    cA
    cc0
    cmin
    co
    #
    cB
    caddc
    co
    #
    cA
    cB
    caddc
    co
    @2
    @4
    cA
    cc0
    cB
    cmin
    co
    #
    cmin
    co
    #
    @6
    @3
    @7
    cA
    cmin
    cB
    df-neg
    oveq2i
    @0
    cc0
    cc
    wcel
    @1
    @8
    @6
    wceq
    0cn
    cA
    cc0
    cB
    subsub
    mp3an2
    syl5eq
    @2
    @5
    cA
    cB
    caddc
    @0
    @5
    cA
    wceq
    @1
    cA
    subid1
    adantr
    oveq1d
    eqtrd
end
