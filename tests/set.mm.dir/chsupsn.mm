include "cch.mm"
include "wcel.mm"
include "csn.mm"
include "chsup.mm"
include "cfv.mm"
include "cuni.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "wceq.mm"
include "snssi.mm"
include "chsupval2.mm"
include "syl.mm"
include "wa.mm"
include "unisng.mm"
include "eqimss.mm"
include "ancli.mm"
include "sseq2.mm"
include "elrab.mm"
include "sylibr.mm"
include "intss1.mm"
include "ssintub.mm"
include "syl6eqssr.mm"
include "eqssd.mm"
include "eqtrd.mm"

theorem chsupsn
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( A e. CH -> ( \/H ` { A } ) = A )

  proof
    cA
    cch
    wcel
    #
    cA
    csn
    #
    chsup
    cfv
    #
    @1
    cuni
    #
    vx
    cv
    #
    wss
    #
    vx
    cch
    crab
    #
    cint
    #
    cA
    @0
    @1
    cch
    wss
    @2
    @7
    wceq
    cA
    cch
    snssi
    vx
    @1
    chsupval2
    syl
    @0
    @7
    cA
    @0
    cA
    @6
    wcel
    #
    @7
    cA
    wss
    @0
    @0
    @3
    cA
    wss
    #
    wa
    @8
    @0
    @9
    @0
    @3
    cA
    wceq
    @9
    cA
    cch
    unisng
    #
    @3
    cA
    eqimss
    syl
    ancli
    @5
    @9
    vx
    cA
    cch
    @4
    cA
    @3
    sseq2
    elrab
    sylibr
    cA
    @6
    intss1
    syl
    @0
    cA
    @3
    @7
    @10
    vx
    @3
    cch
    ssintub
    syl6eqssr
    eqssd
    eqtrd
end
