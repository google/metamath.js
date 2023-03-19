include "wfn.mm"
include "cima.mm"
include "cres.mm"
include "crn.mm"
include "df-ima.mm"
include "fnresdm.mm"
include "rneqd.mm"
include "syl5eq.mm"

theorem fnima
  let cA: class A
  let cF: class F


  assert |- ( F Fn A -> ( F " A ) = ran F )

  proof
    cF
    cA
    wfn
    #
    cF
    cA
    cima
    cF
    cA
    cres
    #
    crn
    cF
    crn
    cF
    cA
    df-ima
    @0
    @1
    cF
    cA
    cF
    fnresdm
    rneqd
    syl5eq
end
