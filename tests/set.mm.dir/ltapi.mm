include "clti.mm"
include "cnpi.mm"
include "cpli.mm"
include "dmaddpi.mm"
include "ltrelpi.mm"
include "0npi.mm"
include "wcel.mm"
include "wbr.mm"
include "co.mm"
include "wb.mm"
include "wa.mm"
include "coa.mm"
include "com.mm"
include "pinn.mm"
include "nnaord.mm"
include "syl3an.mm"
include "3expa.mm"
include "ltpiord.mm"
include "adantr.mm"
include "addclpi.mm"
include "syl2an.mm"
include "wceq.mm"
include "addpiord.mm"
include "adantl.mm"
include "eleq12d.mm"
include "bitrd.mm"
include "anandis.mm"
include "ancoms.mm"
include "3bitr4d.mm"
include "3impa.mm"
include "ndmovord.mm"

theorem ltapi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( C e. N. -> ( A <N B <-> ( C +N A ) <N ( C +N B ) ) )

  proof
    cA
    cB
    cC
    clti
    cnpi
    cpli
    dmaddpi
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
    cpli
    co
    #
    cC
    cB
    cpli
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
    coa
    co
    #
    cC
    cB
    coa
    co
    #
    wcel
    #
    @3
    @6
    @0
    @1
    @2
    @8
    @11
    wb
    #
    @0
    cA
    com
    wcel
    @1
    cB
    com
    wcel
    @2
    cC
    com
    wcel
    @12
    cA
    pinn
    cB
    pinn
    cC
    pinn
    cA
    cB
    cC
    nnaord
    syl3an
    3expa
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
    @13
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
    @14
    @4
    cnpi
    wcel
    @5
    cnpi
    wcel
    @6
    @17
    wb
    @15
    cC
    cA
    addclpi
    cC
    cB
    addclpi
    @4
    @5
    ltpiord
    syl2an
    @16
    @4
    @9
    @5
    @10
    @14
    @4
    @9
    wceq
    @15
    cC
    cA
    addpiord
    adantr
    @15
    @5
    @10
    wceq
    @14
    cC
    cB
    addpiord
    adantl
    eleq12d
    bitrd
    anandis
    ancoms
    3bitr4d
    3impa
    ndmovord
end
