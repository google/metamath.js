include "wcel.mm"
include "cn0.mm"
include "wf.mm"
include "wa.mm"
include "cc0.mm"
include "csupp.mm"
include "co.mm"
include "ccnv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cn.mm"
include "cvv.mm"
include "wceq.mm"
include "c0ex.mm"
include "frnsuppeq.mm"
include "imp.mm"
include "mpanl2.mm"
include "dfn2.mm"
include "eqcomi.mm"
include "imaeq2i.mm"
include "syl6eq.mm"

theorem frnnn0supp
  let cF: class F
  let cI: class I
  let cV: class V


  assert |- ( ( I e. V /\ F : I --> NN0 ) -> ( F supp 0 ) = ( `' F " NN ) )

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
    cF
    cc0
    csupp
    co
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
    @3
    cn
    cima
    @0
    cc0
    cvv
    wcel
    #
    @1
    @2
    @5
    wceq
    #
    c0ex
    @0
    @6
    wa
    @1
    @7
    cn0
    cF
    cI
    cV
    cvv
    cc0
    frnsuppeq
    imp
    mpanl2
    @4
    cn
    @3
    cn
    @4
    dfn2
    eqcomi
    imaeq2i
    syl6eq
end
