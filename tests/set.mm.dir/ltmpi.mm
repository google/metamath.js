include "clti.mm"
include "cnpi.mm"
include "cmi.mm"
include "dmmulpi.mm"
include "ltrelpi.mm"
include "0npi.mm"
include "wcel.mm"
include "wbr.mm"
include "co.mm"
include "wb.mm"
include "wa.mm"
include "comu.mm"
include "com.mm"
include "wi.mm"
include "pinn.mm"
include "c0.mm"
include "elni2.mm"
include "w3a.mm"
include "iba.mm"
include "nnmord.mm"
include "sylan9bbr.mm"
include "3exp1.mm"
include "imp4b.mm"
include "syl5bi.mm"
include "syl2an.mm"
include "imp.mm"
include "ltpiord.mm"
include "adantr.mm"
include "mulclpi.mm"
include "wceq.mm"
include "mulpiord.mm"
include "adantl.mm"
include "eleq12d.mm"
include "bitrd.mm"
include "anandis.mm"
include "ancoms.mm"
include "3bitr4d.mm"
include "3impa.mm"
include "ndmovord.mm"

theorem ltmpi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( C e. N. -> ( A <N B <-> ( C .N A ) <N ( C .N B ) ) )

  proof
    cA
    cB
    cC
    clti
    cnpi
    cmi
    dmmulpi
    ltrelpi
    0npi
    cA
    cnpi
    wcel
    #
    cB
    cnpi
    wcel
    #
    cC
    cnpi
    wcel
    #
    cA
    cB
    clti
    wbr
    #
    cC
    cA
    cmi
    co
    #
    cC
    cB
    cmi
    co
    #
    clti
    wbr
    #
    wb
    @0
    @1
    wa
    #
    @2
    wa
    cA
    cB
    wcel
    #
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
    @3
    @6
    @7
    @2
    @8
    @11
    wb
    #
    @0
    cA
    com
    wcel
    #
    cB
    com
    wcel
    #
    @2
    @12
    wi
    @1
    cA
    pinn
    cB
    pinn
    @2
    cC
    com
    wcel
    #
    c0
    cC
    wcel
    #
    wa
    @13
    @14
    wa
    @12
    cC
    elni2
    @13
    @14
    @15
    @16
    @12
    @13
    @14
    @15
    @16
    @12
    @16
    @8
    @8
    @16
    wa
    @13
    @14
    @15
    w3a
    @11
    @16
    @8
    iba
    cA
    cB
    cC
    nnmord
    sylan9bbr
    3exp1
    imp4b
    syl5bi
    syl2an
    imp
    @7
    @3
    @8
    wb
    @2
    cA
    cB
    ltpiord
    adantr
    @2
    @7
    @6
    @11
    wb
    #
    @2
    @0
    @1
    @17
    @2
    @0
    wa
    #
    @2
    @1
    wa
    #
    wa
    #
    @6
    @4
    @5
    wcel
    #
    @11
    @18
    @4
    cnpi
    wcel
    @5
    cnpi
    wcel
    @6
    @21
    wb
    @19
    cC
    cA
    mulclpi
    cC
    cB
    mulclpi
    @4
    @5
    ltpiord
    syl2an
    @20
    @4
    @9
    @5
    @10
    @18
    @4
    @9
    wceq
    @19
    cC
    cA
    mulpiord
    adantr
    @19
    @5
    @10
    wceq
    @18
    cC
    cB
    mulpiord
    adantl
    eleq12d
    bitrd
    anandis
    ancoms
    3bitr4d
    3impa
    ndmovord
end
