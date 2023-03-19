include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cfv.mm"
include "co.mm"
include "cxp.mm"
include "wf.mm"
include "wceq.mm"
include "subf.mm"
include "opelxpi.mm"
include "fvco3.mm"
include "sylancr.mm"
include "df-ov.mm"
include "fveq1i.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"

theorem cnmetdval
  let cA: class A
  let cB: class B
  let cD: class D
  assume cnmetdval.1: |- D = ( abs o. - )


  assert |- ( ( A e. CC /\ B e. CC ) -> ( A D B ) = ( abs ` ( A - B ) ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    wa
    #
    cA
    cB
    cop
    #
    cabs
    cmin
    ccom
    #
    cfv
    #
    @1
    cmin
    cfv
    #
    cabs
    cfv
    #
    cA
    cB
    cD
    co
    #
    cA
    cB
    cmin
    co
    #
    cabs
    cfv
    @0
    cc
    cc
    cxp
    #
    cc
    cmin
    wf
    @1
    @8
    wcel
    @3
    @5
    wceq
    subf
    cA
    cB
    cc
    cc
    opelxpi
    @8
    cc
    @1
    cabs
    cmin
    fvco3
    sylancr
    @6
    @1
    cD
    cfv
    @3
    cA
    cB
    cD
    df-ov
    @1
    cD
    @2
    cnmetdval.1
    fveq1i
    eqtri
    @7
    @4
    cabs
    cA
    cB
    cmin
    df-ov
    fveq2i
    3eqtr4g
end
