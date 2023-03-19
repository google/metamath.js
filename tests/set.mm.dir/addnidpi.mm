include "cnpi.mm"
include "wcel.mm"
include "wa.mm"
include "cpli.mm"
include "co.mm"
include "wceq.mm"
include "wn.mm"
include "wi.mm"
include "coa.mm"
include "com.mm"
include "pinn.mm"
include "c0.mm"
include "elni2.mm"
include "nnaordi.mm"
include "nna0.mm"
include "eleq1d.mm"
include "word.mm"
include "nnord.mm"
include "ordirr.mm"
include "syl.mm"
include "eleq2.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "con2d.mm"
include "sylbid.mm"
include "adantl.mm"
include "syld.mm"
include "expcom.mm"
include "imp32.mm"
include "sylan2b.mm"
include "sylan.mm"
include "addpiord.mm"
include "eqeq1d.mm"
include "mtbird.mm"
include "a1d.mm"
include "dmaddpi.mm"
include "ndmov.mm"
include "0npi.mm"
include "eleq1.mm"
include "mtbii.mm"
include "syl6bi.mm"
include "pm2.61i.mm"

theorem addnidpi
  let cA: class A
  let cB: class B


  assert |- ( A e. N. -> -. ( A +N B ) = A )

  proof
    cA
    cnpi
    wcel
    #
    cB
    cnpi
    wcel
    #
    wa
    #
    @0
    cA
    cB
    cpli
    co
    #
    cA
    wceq
    #
    wn
    #
    wi
    @2
    @5
    @0
    @2
    @4
    cA
    cB
    coa
    co
    #
    cA
    wceq
    #
    @0
    cA
    com
    wcel
    #
    @1
    @7
    wn
    #
    cA
    pinn
    @1
    @8
    cB
    com
    wcel
    #
    c0
    cB
    wcel
    #
    wa
    @9
    cB
    elni2
    @8
    @10
    @11
    @9
    @10
    @8
    @11
    @9
    wi
    @10
    @8
    wa
    @11
    cA
    c0
    coa
    co
    #
    @6
    wcel
    #
    @9
    c0
    cB
    cA
    nnaordi
    @8
    @13
    @9
    wi
    @10
    @8
    @13
    cA
    @6
    wcel
    #
    @9
    @8
    @12
    cA
    @6
    cA
    nna0
    eleq1d
    @8
    @7
    @14
    @8
    @14
    wn
    @7
    cA
    cA
    wcel
    #
    wn
    #
    @8
    cA
    word
    @16
    cA
    nnord
    cA
    ordirr
    syl
    @7
    @14
    @15
    @6
    cA
    cA
    eleq2
    notbid
    syl5ibrcom
    con2d
    sylbid
    adantl
    syld
    expcom
    imp32
    sylan2b
    sylan
    @2
    @3
    @6
    cA
    cA
    cB
    addpiord
    eqeq1d
    mtbird
    a1d
    @2
    wn
    #
    @4
    @0
    @17
    @4
    c0
    cA
    wceq
    #
    @0
    wn
    @17
    @3
    c0
    cA
    cA
    cB
    cnpi
    cpli
    dmaddpi
    ndmov
    eqeq1d
    @18
    c0
    cnpi
    wcel
    @0
    0npi
    c0
    cA
    cnpi
    eleq1
    mtbii
    syl6bi
    con2d
    pm2.61i
end
