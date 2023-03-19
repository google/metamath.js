include "wfun.mm"
include "ccnv.mm"
include "cres.mm"
include "cima.mm"
include "wceq.mm"
include "funcnvcnv.mm"
include "funcnvres.mm"
include "syl.mm"
include "wrel.mm"
include "funrel.mm"
include "dfrel2.mm"
include "sylib.mm"
include "reseq1d.mm"
include "eqtrd.mm"

theorem funcnvres2
  let cA: class A
  let cF: class F


  assert |- ( Fun F -> `' ( `' F |` A ) = ( F |` ( `' F " A ) ) )

  proof
    cF
    wfun
    #
    cF
    ccnv
    #
    cA
    cres
    ccnv
    #
    @1
    ccnv
    #
    @1
    cA
    cima
    #
    cres
    #
    cF
    @4
    cres
    @0
    @3
    wfun
    @2
    @5
    wceq
    cF
    funcnvcnv
    cA
    @1
    funcnvres
    syl
    @0
    @3
    cF
    @4
    @0
    cF
    wrel
    @3
    cF
    wceq
    cF
    funrel
    cF
    dfrel2
    sylib
    reseq1d
    eqtrd
end
