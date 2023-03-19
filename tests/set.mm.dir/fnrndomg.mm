include "wfn.mm"
include "crn.mm"
include "wfo.mm"
include "wcel.mm"
include "cdom.mm"
include "wbr.mm"
include "dffn4.mm"
include "fodomg.mm"
include "syl5bi.mm"

theorem fnrndomg
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( A e. B -> ( F Fn A -> ran F ~<_ A ) )

  proof
    cF
    cA
    wfn
    cA
    cF
    crn
    #
    cF
    wfo
    cA
    cB
    wcel
    @0
    cA
    cdom
    wbr
    cA
    cF
    dffn4
    cA
    @0
    cB
    cF
    fodomg
    syl5bi
end
