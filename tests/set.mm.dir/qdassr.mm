include "csn.mm"
include "cun.mm"
include "cpr.mm"
include "ctp.mm"
include "unass.mm"
include "df-pr.mm"
include "uneq1i.mm"
include "tpass.mm"
include "uneq2i.mm"
include "3eqtr4i.mm"

theorem qdassr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( { A , B } u. { C , D } ) = ( { A } u. { B , C , D } )

  proof
    cA
    csn
    #
    cB
    csn
    #
    cun
    #
    cC
    cD
    cpr
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
    cpr
    #
    @3
    cun
    @0
    cB
    cC
    cD
    ctp
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
    df-pr
    uneq1i
    @6
    @4
    @0
    cB
    cC
    cD
    tpass
    uneq2i
    3eqtr4i
end
