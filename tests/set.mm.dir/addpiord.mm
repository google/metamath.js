include "cnpi.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cxp.mm"
include "cpli.mm"
include "co.mm"
include "coa.mm"
include "wceq.mm"
include "opelxpi.mm"
include "cres.mm"
include "cfv.mm"
include "fvres.mm"
include "df-ov.mm"
include "df-pli.mm"
include "fveq1i.mm"
include "eqtri.mm"
include "3eqtr4g.mm"
include "syl.mm"

theorem addpiord
  let cA: class A
  let cB: class B


  assert |- ( ( A e. N. /\ B e. N. ) -> ( A +N B ) = ( A +o B ) )

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
    cpli
    co
    #
    cA
    cB
    coa
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
    coa
    @1
    cres
    #
    cfv
    #
    @0
    coa
    cfv
    @3
    @4
    @0
    @1
    coa
    fvres
    @3
    @0
    cpli
    cfv
    @6
    cA
    cB
    cpli
    df-ov
    @0
    cpli
    @5
    df-pli
    fveq1i
    eqtri
    cA
    cB
    coa
    df-ov
    3eqtr4g
    syl
end
