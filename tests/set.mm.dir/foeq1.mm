include "wceq.mm"
include "wfn.mm"
include "crn.mm"
include "wa.mm"
include "wfo.mm"
include "fneq1.mm"
include "rneq.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "df-fo.mm"
include "3bitr4g.mm"

theorem foeq1
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G


  assert |- ( F = G -> ( F : A -onto-> B <-> G : A -onto-> B ) )

  proof
    cF
    cG
    wceq
    #
    cF
    cA
    wfn
    #
    cF
    crn
    #
    cB
    wceq
    #
    wa
    cG
    cA
    wfn
    #
    cG
    crn
    #
    cB
    wceq
    #
    wa
    cA
    cB
    cF
    wfo
    cA
    cB
    cG
    wfo
    @0
    @1
    @4
    @3
    @6
    cA
    cF
    cG
    fneq1
    @0
    @2
    @5
    cB
    cF
    cG
    rneq
    eqeq1d
    anbi12d
    cA
    cB
    cF
    df-fo
    cA
    cB
    cG
    df-fo
    3bitr4g
end
