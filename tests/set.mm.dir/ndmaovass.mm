include "wcel.mm"
include "w3a.mm"
include "wn.mm"
include "caov.mm"
include "cvv.mm"
include "cop.mm"
include "cdm.mm"
include "wceq.mm"
include "wa.mm"
include "cxp.mm"
include "eleq2i.mm"
include "opelxp.mm"
include "bitri.mm"
include "wi.mm"
include "aovvdm.mm"
include "df-3an.mm"
include "simplbi2.mm"
include "sylbi.mm"
include "syl.mm"
include "imp.mm"
include "con3i.mm"
include "ndmaov.mm"
include "3anass.mm"
include "biimpri.mm"
include "a1d.mm"
include "expcom.mm"
include "impcom.mm"
include "pm2.43i.mm"
include "eqtr4d.mm"

theorem ndmaovass
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cF: class F
  let vk: setvar k
  let vx: setvar x
  assume ndmaov.1: |- dom F = ( S X. S )


  assert |- ( -. ( A e. S /\ B e. S /\ C e. S ) -> (( (( A F B )) F C )) = (( A F (( B F C )) )) )

  proof
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    cC
    cS
    wcel
    #
    w3a
    #
    wn
    #
    cA
    cB
    cF
    caov
    #
    cC
    cF
    caov
    #
    cvv
    cA
    cB
    cC
    cF
    caov
    #
    cF
    caov
    #
    @4
    @5
    cC
    cop
    #
    cF
    cdm
    #
    wcel
    #
    wn
    @6
    cvv
    wceq
    @11
    @3
    @11
    @5
    cS
    wcel
    #
    @2
    wa
    #
    @3
    @11
    @9
    cS
    cS
    cxp
    #
    wcel
    @13
    @10
    @14
    @9
    ndmaov.1
    eleq2i
    @5
    cC
    cS
    cS
    opelxp
    bitri
    @12
    @2
    @3
    @12
    cA
    cB
    cop
    #
    @10
    wcel
    #
    @2
    @3
    wi
    #
    cA
    cB
    cS
    cF
    aovvdm
    @16
    @0
    @1
    wa
    #
    @17
    @16
    @15
    @14
    wcel
    @18
    @10
    @14
    @15
    ndmaov.1
    eleq2i
    cA
    cB
    cS
    cS
    opelxp
    bitri
    @3
    @18
    @2
    @0
    @1
    @2
    df-3an
    simplbi2
    sylbi
    syl
    imp
    sylbi
    con3i
    @5
    cC
    cF
    ndmaov
    syl
    @4
    cA
    @7
    cop
    #
    @10
    wcel
    #
    wn
    @8
    cvv
    wceq
    @20
    @3
    @20
    @3
    @20
    @0
    @7
    cS
    wcel
    #
    wa
    #
    @20
    @3
    wi
    #
    @20
    @19
    @14
    wcel
    @22
    @10
    @14
    @19
    ndmaov.1
    eleq2i
    cA
    @7
    cS
    cS
    opelxp
    bitri
    @21
    @0
    @23
    @21
    cB
    cC
    cop
    #
    @10
    wcel
    #
    @0
    @23
    wi
    #
    cB
    cC
    cS
    cF
    aovvdm
    @25
    @1
    @2
    wa
    #
    @26
    @25
    @24
    @14
    wcel
    @27
    @10
    @14
    @24
    ndmaov.1
    eleq2i
    cB
    cC
    cS
    cS
    opelxp
    bitri
    @0
    @27
    @23
    @0
    @27
    wa
    #
    @3
    @20
    @3
    @28
    @0
    @1
    @2
    3anass
    biimpri
    a1d
    expcom
    sylbi
    syl
    impcom
    sylbi
    pm2.43i
    con3i
    cA
    @7
    cF
    ndmaov
    syl
    eqtr4d
end
