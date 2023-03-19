include "wrel.mm"
include "wf1o.mm"
include "ccnv.mm"
include "f1ocnv.mm"
include "wceq.mm"
include "wb.mm"
include "dfrel2.mm"
include "f1oeq1.mm"
include "sylbi.mm"
include "syl5ib.mm"
include "impbid2.mm"

theorem f1ocnvb
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( Rel F -> ( F : A -1-1-onto-> B <-> `' F : B -1-1-onto-> A ) )

  proof
    cF
    wrel
    #
    cA
    cB
    cF
    wf1o
    #
    cB
    cA
    cF
    ccnv
    #
    wf1o
    #
    cA
    cB
    cF
    f1ocnv
    @3
    cA
    cB
    @2
    ccnv
    #
    wf1o
    #
    @0
    @1
    cB
    cA
    @2
    f1ocnv
    @0
    @4
    cF
    wceq
    @5
    @1
    wb
    cF
    dfrel2
    cA
    cB
    @4
    cF
    f1oeq1
    sylbi
    syl5ib
    impbid2
end
