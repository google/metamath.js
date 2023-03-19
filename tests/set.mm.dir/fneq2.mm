include "wceq.mm"
include "wfun.mm"
include "cdm.mm"
include "wa.mm"
include "wfn.mm"
include "eqeq2.mm"
include "anbi2d.mm"
include "df-fn.mm"
include "3bitr4g.mm"

theorem fneq2
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( A = B -> ( F Fn A <-> F Fn B ) )

  proof
    cA
    cB
    wceq
    #
    cF
    wfun
    #
    cF
    cdm
    #
    cA
    wceq
    #
    wa
    @1
    @2
    cB
    wceq
    #
    wa
    cF
    cA
    wfn
    cF
    cB
    wfn
    @0
    @3
    @4
    @1
    cA
    cB
    @2
    eqeq2
    anbi2d
    cF
    cA
    df-fn
    cF
    cB
    df-fn
    3bitr4g
end
