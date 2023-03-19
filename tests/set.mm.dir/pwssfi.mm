include "wcel.mm"
include "cfn.mm"
include "cpw.mm"
include "wss.mm"
include "wi.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "simpl.mm"
include "elpwi.mm"
include "adantl.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"
include "a1i.mm"
include "pwidg.mm"
include "adantr.mm"
include "biimpi.mm"
include "eleq1.mm"
include "rspcva.mm"
include "ex.mm"
include "impbid.mm"

theorem pwssfi
  let cA: class A
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ( A e. Fin <-> ~P A C_ Fin ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cfn
    wcel
    #
    cA
    cpw
    #
    cfn
    wss
    #
    @1
    @3
    wi
    @0
    @1
    vx
    cv
    #
    cfn
    wcel
    #
    vx
    @2
    wral
    #
    @3
    @1
    @5
    vx
    @2
    @1
    @4
    @2
    wcel
    #
    wa
    @1
    @4
    cA
    wss
    #
    @5
    @1
    @7
    simpl
    @7
    @8
    @1
    @4
    cA
    elpwi
    adantl
    cA
    @4
    ssfi
    syl2anc
    ralrimiva
    vx
    @2
    cfn
    dfss3
    #
    sylibr
    a1i
    @0
    @3
    @1
    @0
    @3
    wa
    cA
    @2
    wcel
    #
    @6
    @1
    @0
    @10
    @3
    cA
    cV
    pwidg
    adantr
    @3
    @6
    @0
    @3
    @6
    @9
    biimpi
    adantl
    @5
    @1
    vx
    cA
    @2
    @4
    cA
    cfn
    eleq1
    rspcva
    syl2anc
    ex
    impbid
end
