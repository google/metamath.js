include "cnpi.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cxp.mm"
include "cmi.mm"
include "co.mm"
include "comu.mm"
include "wceq.mm"
include "opelxpi.mm"
include "cres.mm"
include "cfv.mm"
include "fvres.mm"
include "df-ov.mm"
include "df-mi.mm"
include "fveq1i.mm"
include "eqtri.mm"
include "3eqtr4g.mm"
include "syl.mm"

theorem mulpiord
  let cA: class A
  let cB: class B


  assert |- ( ( A e. N. /\ B e. N. ) -> ( A .N B ) = ( A .o B ) )

  proof
    cA
    cnpi
    wcel
    cB
    cnpi
    wcel
    wa
    cA
    cB
    cop
    #
    cnpi
    cnpi
    cxp
    #
    wcel
    #
    cA
    cB
    cmi
    co
    #
    cA
    cB
    comu
    co
    #
    wceq
    cA
    cB
    cnpi
    cnpi
    opelxpi
    @2
    @0
    comu
    @1
    cres
    #
    cfv
    #
    @0
    comu
    cfv
    @3
    @4
    @0
    @1
    comu
    fvres
    @3
    @0
    cmi
    cfv
    @6
    cA
    cB
    cmi
    df-ov
    @0
    cmi
    @5
    df-mi
    fveq1i
    eqtri
    cA
    cB
    comu
    df-ov
    3eqtr4g
    syl
end
