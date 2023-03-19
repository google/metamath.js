include "chil.mm"
include "wcel.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "cch.mm"
include "csh.mm"
include "spansnch.mm"
include "chsh.mm"
include "syl.mm"

theorem spansnsh
  let cA: class A


  assert |- ( A e. ~H -> ( span ` { A } ) e. SH )

  proof
    cA
    chil
    wcel
    cA
    csn
    cspn
    cfv
    #
    cch
    wcel
    @0
    csh
    wcel
    cA
    spansnch
    @0
    chsh
    syl
end
