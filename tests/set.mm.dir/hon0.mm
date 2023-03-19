include "chil.mm"
include "wf.mm"
include "c0.mm"
include "wceq.mm"
include "c0v.mm"
include "ax-hv0cl.mm"
include "n0ii.mm"
include "wfn.mm"
include "fn0.mm"
include "wi.mm"
include "ffn.mm"
include "fndmu.mm"
include "ex.mm"
include "syl.mm"
include "syl5bir.mm"
include "mtoi.mm"

theorem hon0
  let cT: class T


  assert |- ( T : ~H --> ~H -> -. T = (/) )

  proof
    chil
    chil
    cT
    wf
    #
    cT
    c0
    wceq
    #
    chil
    c0
    wceq
    #
    c0v
    chil
    ax-hv0cl
    n0ii
    @1
    cT
    c0
    wfn
    #
    @0
    @2
    cT
    fn0
    @0
    cT
    chil
    wfn
    #
    @3
    @2
    wi
    chil
    chil
    cT
    ffn
    @4
    @3
    @2
    chil
    c0
    cT
    fndmu
    ex
    syl
    syl5bir
    mtoi
end
