include "csuc.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "wi.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "en2lp.mm"
include "ianor.mm"
include "mpbi.mm"
include "sucidg.mm"
include "eleq2.mm"
include "syl5ibcom.mm"
include "elsucg.mm"
include "sylibd.mm"
include "imp.mm"
include "ord.mm"
include "ex.mm"
include "com23.mm"
include "syl5ibrcom.mm"
include "eqcom.mm"
include "syl6ib.mm"
include "jaao.mm"
include "mpi.mm"
include "sucexb.mm"
include "notbii.mm"
include "nelneq.mm"
include "syl2anb.mm"
include "pm2.21d.mm"
include "ancoms.mm"
include "syl5bi.mm"
include "sucprc.mm"
include "eqeqan12d.mm"
include "biimpd.mm"
include "4cases.mm"
include "suceq.mm"
include "impbii.mm"

theorem suc11reg
  let cA: class A
  let cB: class B


  assert |- ( suc A = suc B <-> A = B )

  proof
    cA
    csuc
    #
    cB
    csuc
    #
    wceq
    #
    cA
    cB
    wceq
    #
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    @2
    @3
    wi
    #
    @4
    @5
    wa
    cA
    cB
    wcel
    #
    wn
    #
    cB
    cA
    wcel
    #
    wn
    #
    wo
    #
    @6
    @7
    @9
    wa
    wn
    @11
    cA
    cB
    en2lp
    @7
    @9
    ianor
    mpbi
    @4
    @8
    @6
    @5
    @10
    @4
    @2
    @8
    @3
    @4
    @2
    @8
    @3
    wi
    @4
    @2
    wa
    @7
    @3
    @4
    @2
    @7
    @3
    wo
    #
    @4
    @2
    cA
    @1
    wcel
    #
    @12
    @4
    cA
    @0
    wcel
    @2
    @13
    cA
    cvv
    sucidg
    @0
    @1
    cA
    eleq2
    syl5ibcom
    cA
    cB
    cvv
    elsucg
    sylibd
    imp
    ord
    ex
    com23
    @5
    @2
    @10
    @3
    @5
    @2
    @10
    @3
    wi
    @5
    @2
    wa
    #
    @10
    cB
    cA
    wceq
    #
    @3
    @14
    @9
    @15
    @5
    @2
    @9
    @15
    wo
    #
    @5
    @2
    cB
    @0
    wcel
    #
    @16
    @5
    @17
    @2
    cB
    @1
    wcel
    cB
    cvv
    sucidg
    @0
    @1
    cB
    eleq2
    syl5ibrcom
    cB
    cA
    cvv
    elsucg
    sylibd
    imp
    ord
    cB
    cA
    eqcom
    syl6ib
    ex
    com23
    jaao
    mpi
    @4
    @5
    wn
    #
    wa
    @2
    @3
    @4
    @0
    cvv
    wcel
    #
    @1
    cvv
    wcel
    #
    wn
    @2
    wn
    @18
    cA
    sucexb
    #
    @5
    @20
    cB
    sucexb
    #
    notbii
    @0
    @1
    cvv
    nelneq
    syl2anb
    pm2.21d
    @2
    @1
    @0
    wceq
    #
    @4
    wn
    #
    @5
    wa
    #
    @3
    @0
    @1
    eqcom
    @25
    @23
    @3
    @5
    @24
    @23
    wn
    #
    @5
    @20
    @19
    wn
    @26
    @24
    @22
    @4
    @19
    @21
    notbii
    @1
    @0
    cvv
    nelneq
    syl2anb
    ancoms
    pm2.21d
    syl5bi
    @24
    @18
    wa
    @2
    @3
    @24
    @18
    @0
    cA
    @1
    cB
    cA
    sucprc
    cB
    sucprc
    eqeqan12d
    biimpd
    4cases
    cA
    cB
    suceq
    impbii
end
