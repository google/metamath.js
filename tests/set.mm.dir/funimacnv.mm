include "wfun.mm"
include "ccnv.mm"
include "cima.mm"
include "cres.mm"
include "crn.mm"
include "cin.mm"
include "funcnvres2.mm"
include "rneqd.mm"
include "df-ima.mm"
include "syl6reqr.mm"
include "cdm.mm"
include "df-rn.mm"
include "ineq2i.mm"
include "dmres.mm"
include "dfdm4.mm"
include "3eqtr2ri.mm"
include "syl6eq.mm"

theorem funimacnv
  let cA: class A
  let cF: class F


  assert |- ( Fun F -> ( F " ( `' F " A ) ) = ( A i^i ran F ) )

  proof
    cF
    wfun
    #
    cF
    cF
    ccnv
    #
    cA
    cima
    #
    cima
    #
    @1
    cA
    cres
    #
    ccnv
    #
    crn
    #
    cA
    cF
    crn
    #
    cin
    #
    @0
    @6
    cF
    @2
    cres
    #
    crn
    @3
    @0
    @5
    @9
    cA
    cF
    funcnvres2
    rneqd
    cF
    @2
    df-ima
    syl6reqr
    @8
    cA
    @1
    cdm
    #
    cin
    @4
    cdm
    @6
    @7
    @10
    cA
    cF
    df-rn
    ineq2i
    @1
    cA
    dmres
    @4
    dfdm4
    3eqtr2ri
    syl6eq
end
