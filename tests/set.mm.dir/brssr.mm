include "wcel.mm"
include "cssr.mm"
include "wbr.mm"
include "wss.mm"
include "cvv.mm"
include "wa.mm"
include "relssr.mm"
include "brrelexi.mm"
include "adantl.mm"
include "simpl.mm"
include "jca.mm"
include "ssexg.mm"
include "simpr.mm"
include "ancoms.mm"
include "cv.mm"
include "sseq1.mm"
include "sseq2.mm"
include "df-ssr.mm"
include "brabg.mm"
include "pm5.21nd.mm"

theorem brssr
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( B e. V -> ( A _S B <-> A C_ B ) )

  proof
    cB
    cV
    wcel
    #
    cA
    cB
    cssr
    wbr
    #
    cA
    cB
    wss
    #
    cA
    cvv
    wcel
    #
    @0
    wa
    #
    @0
    @1
    wa
    @3
    @0
    @1
    @3
    @0
    cA
    cB
    cssr
    relssr
    brrelexi
    adantl
    @0
    @1
    simpl
    jca
    @2
    @0
    @4
    @2
    @0
    wa
    @3
    @0
    cA
    cB
    cV
    ssexg
    @2
    @0
    simpr
    jca
    ancoms
    vx
    cv
    #
    vy
    cv
    #
    wss
    cA
    @6
    wss
    @2
    vx
    vy
    cA
    cB
    cvv
    cV
    cssr
    @5
    cA
    @6
    sseq1
    @6
    cB
    cA
    sseq2
    vx
    vy
    df-ssr
    brabg
    pm5.21nd
end
