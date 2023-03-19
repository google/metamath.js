include "wcel.mm"
include "crpss.mm"
include "wbr.mm"
include "wpss.mm"
include "cvv.mm"
include "wa.mm"
include "elex.mm"
include "relrpss.mm"
include "brrelexi.mm"
include "anim12i.mm"
include "adantr.mm"
include "wss.mm"
include "pssss.mm"
include "ssexg.mm"
include "syl2anr.mm"
include "jca.mm"
include "wb.mm"
include "cv.mm"
include "psseq1.mm"
include "psseq2.mm"
include "df-rpss.mm"
include "brabg.mm"
include "ancoms.mm"
include "pm5.21nd.mm"

theorem brrpssg
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( B e. V -> ( A [C.] B <-> A C. B ) )

  proof
    cB
    cV
    wcel
    #
    cA
    cB
    crpss
    wbr
    #
    cA
    cB
    wpss
    #
    cB
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    wa
    @0
    @3
    @1
    @4
    cB
    cV
    elex
    #
    cA
    cB
    crpss
    relrpss
    brrelexi
    anim12i
    @0
    @2
    wa
    @3
    @4
    @0
    @3
    @2
    @5
    adantr
    @2
    cA
    cB
    wss
    @3
    @4
    @0
    cA
    cB
    pssss
    @5
    cA
    cB
    cvv
    ssexg
    syl2anr
    jca
    @4
    @3
    @1
    @2
    wb
    vx
    cv
    #
    vy
    cv
    #
    wpss
    cA
    @7
    wpss
    @2
    vx
    vy
    cA
    cB
    cvv
    cvv
    crpss
    @6
    cA
    @7
    psseq1
    @7
    cB
    cA
    psseq2
    vx
    vy
    df-rpss
    brabg
    ancoms
    pm5.21nd
end
