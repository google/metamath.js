include "cima.mm"
include "wss.mm"
include "cres.mm"
include "crn.mm"
include "cdm.mm"
include "wa.mm"
include "cxp.mm"
include "df-ima.mm"
include "sseq1i.mm"
include "cin.mm"
include "dmres.mm"
include "inss1.mm"
include "eqsstri.mm"
include "biantrur.mm"
include "wrel.mm"
include "relres.mm"
include "relssdmrn.mm"
include "ax-mp.mm"
include "xpss12.mm"
include "syl5ss.mm"
include "dmss.mm"
include "dmxpss.mm"
include "syl6ss.mm"
include "rnss.mm"
include "rnxpss.mm"
include "jca.mm"
include "impbii.mm"
include "3bitri.mm"

theorem rp-imass
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( ( R " A ) C_ B <-> ( R |` A ) C_ ( A X. B ) )

  proof
    cR
    cA
    cima
    #
    cB
    wss
    cR
    cA
    cres
    #
    crn
    #
    cB
    wss
    #
    @1
    cdm
    #
    cA
    wss
    #
    @3
    wa
    #
    @1
    cA
    cB
    cxp
    #
    wss
    #
    @0
    @2
    cB
    cR
    cA
    df-ima
    sseq1i
    @5
    @3
    @4
    cA
    cR
    cdm
    #
    cin
    cA
    cR
    cA
    dmres
    cA
    @9
    inss1
    eqsstri
    biantrur
    @6
    @8
    @6
    @1
    @4
    @2
    cxp
    #
    @7
    @1
    wrel
    @1
    @10
    wss
    cR
    cA
    relres
    @1
    relssdmrn
    ax-mp
    @4
    cA
    @2
    cB
    xpss12
    syl5ss
    @8
    @5
    @3
    @8
    @4
    @7
    cdm
    cA
    @1
    @7
    dmss
    cA
    cB
    dmxpss
    syl6ss
    @8
    @2
    @7
    crn
    cB
    @1
    @7
    rnss
    cA
    cB
    rnxpss
    syl6ss
    jca
    impbii
    3bitri
end
