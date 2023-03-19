include "chil.mm"
include "wcel.mm"
include "chio.mm"
include "cfv.mm"
include "cpjh.mm"
include "df-iop.mm"
include "fveq1i.mm"
include "pjch1.mm"
include "syl5eq.mm"

theorem hoival
  let cA: class A


  assert |- ( A e. ~H -> ( Iop ` A ) = A )

  proof
    cA
    chil
    wcel
    cA
    chio
    cfv
    cA
    chil
    cpjh
    cfv
    #
    cfv
    cA
    cA
    chio
    @0
    df-iop
    fveq1i
    cA
    pjch1
    syl5eq
end
