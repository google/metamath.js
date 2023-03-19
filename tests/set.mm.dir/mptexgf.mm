include "wcel.mm"
include "cmpt.mm"
include "wfun.mm"
include "cdm.mm"
include "cvv.mm"
include "funmpt.mm"
include "wss.mm"
include "crab.mm"
include "eqid.mm"
include "dmmpt.mm"
include "wtru.mm"
include "wi.mm"
include "wral.mm"
include "a1tru.mm"
include "rgenw.mm"
include "ss2rab.mm"
include "mpbir.mm"
include "rabtru.mm"
include "sseqtri.mm"
include "eqsstri.mm"
include "ssexg.mm"
include "mpan.mm"
include "funex.mm"
include "sylancr.mm"

theorem mptexgf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  assume mptexgf.a: |- F/_ x A


  assert |- ( A e. V -> ( x e. A |-> B ) e. _V )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    cB
    cmpt
    #
    wfun
    @1
    cdm
    #
    cvv
    wcel
    #
    @1
    cvv
    wcel
    vx
    cA
    cB
    funmpt
    @2
    cA
    wss
    @0
    @3
    @2
    cB
    cvv
    wcel
    #
    vx
    cA
    crab
    #
    cA
    vx
    cA
    cB
    @1
    @1
    eqid
    dmmpt
    @5
    wtru
    vx
    cA
    crab
    #
    cA
    @5
    @6
    wss
    @4
    wtru
    wi
    #
    vx
    cA
    wral
    @7
    vx
    cA
    @4
    a1tru
    rgenw
    @4
    wtru
    vx
    cA
    ss2rab
    mpbir
    vx
    cA
    mptexgf.a
    rabtru
    sseqtri
    eqsstri
    @2
    cA
    cV
    ssexg
    mpan
    cvv
    @1
    funex
    sylancr
end
