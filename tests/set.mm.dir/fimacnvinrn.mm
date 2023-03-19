include "wfun.mm"
include "ccnv.mm"
include "crn.mm"
include "cin.mm"
include "cima.mm"
include "cdm.mm"
include "inpreima.mm"
include "wf.mm"
include "wceq.mm"
include "wfo.mm"
include "funforn.mm"
include "fof.mm"
include "sylbi.mm"
include "fimacnv.mm"
include "syl.mm"
include "ineq2d.mm"
include "cres.mm"
include "cnvresima.mm"
include "resdm2.mm"
include "wrel.mm"
include "funrel.mm"
include "dfrel2.mm"
include "sylib.mm"
include "syl5eq.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "syl5eqr.mm"
include "3eqtrrd.mm"

theorem fimacnvinrn
  let cA: class A
  let cF: class F


  assert |- ( Fun F -> ( `' F " A ) = ( `' F " ( A i^i ran F ) ) )

  proof
    cF
    wfun
    #
    cF
    ccnv
    #
    cA
    cF
    crn
    #
    cin
    cima
    @1
    cA
    cima
    #
    @1
    @2
    cima
    #
    cin
    @3
    cF
    cdm
    #
    cin
    #
    @3
    cA
    @2
    cF
    inpreima
    @0
    @4
    @5
    @3
    @0
    @5
    @2
    cF
    wf
    #
    @4
    @5
    wceq
    @0
    @5
    @2
    cF
    wfo
    @7
    cF
    funforn
    @5
    @2
    cF
    fof
    sylbi
    @5
    @2
    cF
    fimacnv
    syl
    ineq2d
    @0
    @6
    cF
    @5
    cres
    #
    ccnv
    #
    cA
    cima
    @3
    @5
    cA
    cF
    cnvresima
    @0
    @9
    @1
    cA
    @0
    @8
    cF
    @0
    @8
    @1
    ccnv
    #
    cF
    cF
    resdm2
    @0
    cF
    wrel
    @10
    cF
    wceq
    cF
    funrel
    cF
    dfrel2
    sylib
    syl5eq
    cnveqd
    imaeq1d
    syl5eqr
    3eqtrrd
end
