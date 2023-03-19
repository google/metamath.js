include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "ctp.mm"
include "unass.mm"
include "df-tp.mm"
include "uneq1i.mm"
include "df-pr.mm"
include "uneq2i.mm"
include "3eqtr4ri.mm"

theorem qdass
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( { A , B } u. { C , D } ) = ( { A , B , C } u. { D } )

  proof
    cA
    cB
    cpr
    #
    cC
    csn
    #
    cun
    #
    cD
    csn
    #
    cun
    @0
    @1
    @3
    cun
    #
    cun
    cA
    cB
    cC
    ctp
    #
    @3
    cun
    @0
    cC
    cD
    cpr
    #
    cun
    @0
    @1
    @3
    unass
    @5
    @2
    @3
    cA
    cB
    cC
    df-tp
    uneq1i
    @6
    @4
    @0
    cC
    cD
    df-pr
    uneq2i
    3eqtr4ri
end
