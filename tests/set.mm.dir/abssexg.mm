include "wcel.mm"
include "cpw.mm"
include "cvv.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "cab.mm"
include "pwexg.mm"
include "df-pw.mm"
include "eleq1i.mm"
include "simpl.mm"
include "ss2abi.mm"
include "ssexg.mm"
include "mpan.mm"
include "sylbi.mm"
include "syl.mm"

theorem abssexg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V

  disjoint A x
  assert |- ( A e. V -> { x | ( x C_ A /\ ph ) } e. _V )

  proof
    cA
    cV
    wcel
    cA
    cpw
    #
    cvv
    wcel
    #
    vx
    cv
    cA
    wss
    #
    wph
    wa
    #
    vx
    cab
    #
    cvv
    wcel
    #
    cA
    cV
    pwexg
    @1
    @2
    vx
    cab
    #
    cvv
    wcel
    #
    @5
    @0
    @6
    cvv
    vx
    cA
    df-pw
    eleq1i
    @4
    @6
    wss
    @7
    @5
    @3
    @2
    vx
    @2
    wph
    simpl
    ss2abi
    @4
    @6
    cvv
    ssexg
    mpan
    sylbi
    syl
end
