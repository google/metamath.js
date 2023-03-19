include "c1o.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "wceq.mm"
include "df1o2.mm"
include "eleq2i.mm"
include "0ex.mm"
include "elsn2.mm"
include "bitri.mm"

theorem el1o
  let cA: class A


  assert |- ( A e. 1o <-> A = (/) )

  proof
    cA
    c1o
    wcel
    cA
    c0
    csn
    #
    wcel
    cA
    c0
    wceq
    c1o
    @0
    cA
    df1o2
    eleq2i
    cA
    c0
    0ex
    elsn2
    bitri
end
