include "clti.mm"
include "wbr.mm"
include "cep.mm"
include "cnpi.mm"
include "cxp.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "df-lti.mm"
include "breqi.mm"
include "brinxp.mm"
include "wb.mm"
include "epelg.mm"
include "adantl.mm"
include "bitr3d.mm"
include "syl5bb.mm"

theorem ltpiord
  let cA: class A
  let cB: class B


  assert |- ( ( A e. N. /\ B e. N. ) -> ( A <N B <-> A e. B ) )

  proof
    cA
    cB
    clti
    wbr
    cA
    cB
    cep
    cnpi
    cnpi
    cxp
    cin
    #
    wbr
    #
    cA
    cnpi
    wcel
    #
    cB
    cnpi
    wcel
    #
    wa
    #
    cA
    cB
    wcel
    #
    cA
    cB
    clti
    @0
    df-lti
    breqi
    @4
    cA
    cB
    cep
    wbr
    #
    @1
    @5
    cA
    cB
    cnpi
    cnpi
    cep
    brinxp
    @3
    @6
    @5
    wb
    @2
    cA
    cB
    cnpi
    epelg
    adantl
    bitr3d
    syl5bb
end
