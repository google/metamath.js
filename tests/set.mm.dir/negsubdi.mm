include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "cneg.mm"
include "wceq.mm"
include "0cn.mm"
include "subsub.mm"
include "mp3an1.mm"
include "df-neg.mm"
include "oveq1i.mm"
include "3eqtr4g.mm"

theorem negsubdi
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> -u ( A - B ) = ( -u A + B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    cc0
    cA
    cB
    cmin
    co
    #
    cmin
    co
    #
    cc0
    cA
    cmin
    co
    #
    cB
    caddc
    co
    #
    @2
    cneg
    cA
    cneg
    #
    cB
    caddc
    co
    cc0
    cc
    wcel
    @0
    @1
    @3
    @5
    wceq
    0cn
    cc0
    cA
    cB
    subsub
    mp3an1
    @2
    df-neg
    @6
    @4
    cB
    caddc
    cA
    df-neg
    oveq1i
    3eqtr4g
end
