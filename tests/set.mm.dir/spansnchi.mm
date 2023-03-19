include "chil.mm"
include "wcel.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "cch.mm"
include "spansnch.mm"
include "ax-mp.mm"

theorem spansnchi
  let cA: class A
  assume spansnch.1: |- A e. ~H


  assert |- ( span ` { A } ) e. CH

  proof
    cA
    chil
    wcel
    cA
    csn
    cspn
    cfv
    cch
    wcel
    spansnch.1
    cA
    spansnch
    ax-mp
end
