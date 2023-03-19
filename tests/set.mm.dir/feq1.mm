include "wceq.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "wf.mm"
include "fneq1.mm"
include "rneq.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "df-f.mm"
include "3bitr4g.mm"

theorem feq1
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G


  assert |- ( F = G -> ( F : A --> B <-> G : A --> B ) )

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
    wss
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
    wss
    #
    wa
    cA
    cB
    cF
    wf
    cA
    cB
    cG
    wf
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
    sseq1d
    anbi12d
    cA
    cB
    cF
    df-f
    cA
    cB
    cG
    df-f
    3bitr4g
end
