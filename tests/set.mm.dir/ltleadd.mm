include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "caddc.mm"
include "co.mm"
include "wb.mm"
include "ltadd1.mm"
include "3com23.mm"
include "3expa.mm"
include "adantrr.mm"
include "leadd2.mm"
include "3expb.mm"
include "adantll.mm"
include "anbi12d.mm"
include "wi.mm"
include "readdcl.mm"
include "adantr.mm"
include "ancoms.mm"
include "ad2ant2lr.mm"
include "adantl.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "sylbid.mm"

theorem ltleadd
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( C e. RR /\ D e. RR ) ) -> ( ( A < C /\ B <_ D ) -> ( A + B ) < ( C + D ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cC
    cr
    wcel
    #
    cD
    cr
    wcel
    #
    wa
    #
    wa
    #
    cA
    cC
    clt
    wbr
    #
    cB
    cD
    cle
    wbr
    #
    wa
    cA
    cB
    caddc
    co
    #
    cC
    cB
    caddc
    co
    #
    clt
    wbr
    #
    @10
    cC
    cD
    caddc
    co
    #
    cle
    wbr
    #
    wa
    #
    @9
    @12
    clt
    wbr
    #
    @6
    @7
    @11
    @8
    @13
    @2
    @3
    @7
    @11
    wb
    #
    @4
    @0
    @1
    @3
    @16
    @0
    @3
    @1
    @16
    cA
    cC
    cB
    ltadd1
    3com23
    3expa
    adantrr
    @1
    @5
    @8
    @13
    wb
    #
    @0
    @1
    @3
    @4
    @17
    @1
    @4
    @3
    @17
    cB
    cD
    cC
    leadd2
    3com23
    3expb
    adantll
    anbi12d
    @6
    @9
    cr
    wcel
    #
    @10
    cr
    wcel
    #
    @12
    cr
    wcel
    #
    @14
    @15
    wi
    @2
    @18
    @5
    cA
    cB
    readdcl
    adantr
    @1
    @3
    @19
    @0
    @4
    @3
    @1
    @19
    cC
    cB
    readdcl
    ancoms
    ad2ant2lr
    @5
    @20
    @2
    cC
    cD
    readdcl
    adantl
    @9
    @10
    @12
    ltletr
    syl3anc
    sylbid
end
