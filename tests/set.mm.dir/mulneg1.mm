include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "cneg.mm"
include "wceq.mm"
include "0cn.mm"
include "subdir.mm"
include "mp3an1.mm"
include "simpr.mm"
include "mul02d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "df-neg.mm"
include "oveq1i.mm"
include "3eqtr4g.mm"

theorem mulneg1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( -u A x. B ) = -u ( A x. B ) )

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
    #
    cc0
    cA
    cmin
    co
    #
    cB
    cmul
    co
    #
    cc0
    cA
    cB
    cmul
    co
    #
    cmin
    co
    #
    cA
    cneg
    #
    cB
    cmul
    co
    @5
    cneg
    @2
    @4
    cc0
    cB
    cmul
    co
    #
    @5
    cmin
    co
    #
    @6
    cc0
    cc
    wcel
    @0
    @1
    @4
    @9
    wceq
    0cn
    cc0
    cA
    cB
    subdir
    mp3an1
    @2
    @8
    cc0
    @5
    cmin
    @2
    cB
    @0
    @1
    simpr
    mul02d
    oveq1d
    eqtrd
    @7
    @3
    cB
    cmul
    cA
    df-neg
    oveq1i
    @5
    df-neg
    3eqtr4g
end
