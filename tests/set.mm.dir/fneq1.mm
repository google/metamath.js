include "wceq.mm"
include "wfun.mm"
include "cdm.mm"
include "wa.mm"
include "wfn.mm"
include "funeq.mm"
include "dmeq.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "df-fn.mm"
include "3bitr4g.mm"

theorem fneq1
  let cA: class A
  let cF: class F
  let cG: class G


  assert |- ( F = G -> ( F Fn A <-> G Fn A ) )

  proof
    cF
    cG
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
    cG
    wfun
    #
    cG
    cdm
    #
    cA
    wceq
    #
    wa
    cF
    cA
    wfn
    cG
    cA
    wfn
    @0
    @1
    @4
    @3
    @6
    cF
    cG
    funeq
    @0
    @2
    @5
    cA
    cF
    cG
    dmeq
    eqeq1d
    anbi12d
    cF
    cA
    df-fn
    cG
    cA
    df-fn
    3bitr4g
end
