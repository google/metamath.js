include "wcel.mm"
include "cn0.mm"
include "wf.mm"
include "wa.mm"
include "cc0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "ccnv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cfn.mm"
include "cn.mm"
include "wb.mm"
include "cvv.mm"
include "wi.mm"
include "c0ex.mm"
include "frnfsuppbi.mm"
include "mpan2.mm"
include "imp.mm"
include "wceq.mm"
include "dfn2.mm"
include "eqcomi.mm"
include "a1i.mm"
include "imaeq2d.mm"
include "eleq1d.mm"
include "bitrd.mm"

theorem frnnn0fsupp
  let cF: class F
  let cI: class I
  let cV: class V


  assert |- ( ( I e. V /\ F : I --> NN0 ) -> ( F finSupp 0 <-> ( `' F " NN ) e. Fin ) )

  proof
    cI
    cV
    wcel
    #
    cI
    cn0
    cF
    wf
    #
    wa
    #
    cF
    cc0
    cfsupp
    wbr
    #
    cF
    ccnv
    #
    cn0
    cc0
    csn
    cdif
    #
    cima
    #
    cfn
    wcel
    #
    @4
    cn
    cima
    #
    cfn
    wcel
    @0
    @1
    @3
    @7
    wb
    #
    @0
    cc0
    cvv
    wcel
    @1
    @9
    wi
    c0ex
    cn0
    cF
    cI
    cV
    cvv
    cc0
    frnfsuppbi
    mpan2
    imp
    @2
    @6
    @8
    cfn
    @2
    @5
    cn
    @4
    @5
    cn
    wceq
    @2
    cn
    @5
    dfn2
    eqcomi
    a1i
    imaeq2d
    eleq1d
    bitrd
end
