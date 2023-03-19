include "cin.mm"
include "ccnv.mm"
include "cdm.mm"
include "crn.mm"
include "cnvin.mm"
include "dmeqi.mm"
include "dmin.mm"
include "eqsstri.mm"
include "df-rn.mm"
include "ineq12i.mm"
include "3sstr4i.mm"

theorem rnin
  let cA: class A
  let cB: class B


  assert |- ran ( A i^i B ) C_ ( ran A i^i ran B )

  proof
    cA
    cB
    cin
    #
    ccnv
    #
    cdm
    #
    cA
    ccnv
    #
    cdm
    #
    cB
    ccnv
    #
    cdm
    #
    cin
    #
    @0
    crn
    cA
    crn
    #
    cB
    crn
    #
    cin
    @2
    @3
    @5
    cin
    #
    cdm
    @7
    @1
    @10
    cA
    cB
    cnvin
    dmeqi
    @3
    @5
    dmin
    eqsstri
    @0
    df-rn
    @8
    @4
    @9
    @6
    cA
    df-rn
    cB
    df-rn
    ineq12i
    3sstr4i
end
