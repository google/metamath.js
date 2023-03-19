include "wfun.mm"
include "wcel.mm"
include "wa.mm"
include "cres.mm"
include "cdm.mm"
include "cvv.mm"
include "crn.mm"
include "cxp.mm"
include "dmresexg.mm"
include "adantl.mm"
include "cima.mm"
include "df-ima.mm"
include "funimaexg.mm"
include "syl5eqelr.mm"
include "jca.mm"
include "xpexg.mm"
include "wss.mm"
include "wrel.mm"
include "relres.mm"
include "relssdmrn.mm"
include "ax-mp.mm"
include "ssexg.mm"
include "mpan.mm"
include "3syl.mm"

theorem resfunexgALT
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( Fun A /\ B e. C ) -> ( A |` B ) e. _V )

  proof
    cA
    wfun
    #
    cB
    cC
    wcel
    #
    wa
    #
    cA
    cB
    cres
    #
    cdm
    #
    cvv
    wcel
    #
    @3
    crn
    #
    cvv
    wcel
    #
    wa
    @4
    @6
    cxp
    #
    cvv
    wcel
    #
    @3
    cvv
    wcel
    #
    @2
    @5
    @7
    @1
    @5
    @0
    cA
    cB
    cC
    dmresexg
    adantl
    @2
    @6
    cA
    cB
    cima
    cvv
    cA
    cB
    df-ima
    cA
    cB
    cC
    funimaexg
    syl5eqelr
    jca
    @4
    @6
    cvv
    cvv
    xpexg
    @3
    @8
    wss
    #
    @9
    @10
    @3
    wrel
    @11
    cA
    cB
    relres
    @3
    relssdmrn
    ax-mp
    @3
    @8
    cvv
    ssexg
    mpan
    3syl
end
