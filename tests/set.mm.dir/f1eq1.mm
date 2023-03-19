include "wceq.mm"
include "wf.mm"
include "ccnv.mm"
include "wfun.mm"
include "wa.mm"
include "wf1.mm"
include "feq1.mm"
include "cnveq.mm"
include "funeqd.mm"
include "anbi12d.mm"
include "df-f1.mm"
include "3bitr4g.mm"

theorem f1eq1
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G


  assert |- ( F = G -> ( F : A -1-1-> B <-> G : A -1-1-> B ) )

  proof
    cF
    cG
    wceq
    #
    cA
    cB
    cF
    wf
    #
    cF
    ccnv
    #
    wfun
    #
    wa
    cA
    cB
    cG
    wf
    #
    cG
    ccnv
    #
    wfun
    #
    wa
    cA
    cB
    cF
    wf1
    cA
    cB
    cG
    wf1
    @0
    @1
    @4
    @3
    @6
    cA
    cB
    cF
    cG
    feq1
    @0
    @2
    @5
    cF
    cG
    cnveq
    funeqd
    anbi12d
    cA
    cB
    cF
    df-f1
    cA
    cB
    cG
    df-f1
    3bitr4g
end
