include "cc.mm"
include "wcel.mm"
include "c0p.mm"
include "cfv.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "df-0p.mm"
include "fveq1i.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "syl5eq.mm"

theorem 0pval
  let cA: class A


  assert |- ( A e. CC -> ( 0p ` A ) = 0 )

  proof
    cA
    cc
    wcel
    cA
    c0p
    cfv
    cA
    cc
    cc0
    csn
    cxp
    #
    cfv
    cc0
    cA
    c0p
    @0
    df-0p
    fveq1i
    cc
    cc0
    cA
    c0ex
    fvconst2
    syl5eq
end
