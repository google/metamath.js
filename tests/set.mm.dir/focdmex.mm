include "wcel.mm"
include "wfo.mm"
include "wa.mm"
include "crn.mm"
include "cvv.mm"
include "wf.mm"
include "fof.mm"
include "anim2i.mm"
include "ancomd.mm"
include "fex.mm"
include "rnexg.mm"
include "3syl.mm"
include "wb.mm"
include "forn.mm"
include "eleq1d.mm"
include "adantl.mm"
include "mpbid.mm"

theorem focdmex
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V


  assert |- ( ( A e. V /\ F : A -onto-> B ) -> B e. _V )

  proof
    cA
    cV
    wcel
    #
    cA
    cB
    cF
    wfo
    #
    wa
    #
    cF
    crn
    #
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    @2
    cA
    cB
    cF
    wf
    #
    @0
    wa
    cF
    cvv
    wcel
    @4
    @2
    @0
    @6
    @1
    @6
    @0
    cA
    cB
    cF
    fof
    anim2i
    ancomd
    cA
    cB
    cV
    cF
    fex
    cF
    cvv
    rnexg
    3syl
    @1
    @4
    @5
    wb
    @0
    @1
    @3
    cB
    cvv
    cA
    cB
    cF
    forn
    eleq1d
    adantl
    mpbid
end
