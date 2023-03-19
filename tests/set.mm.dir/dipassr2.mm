include "ccphlo.mm"
include "wcel.mm"
include "cc.mm"
include "w3a.mm"
include "wa.mm"
include "ccj.mm"
include "cfv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "cjcl.mm"
include "dipassr.mm"
include "syl3anr2.mm"
include "cjcj.mm"
include "3ad2ant2.mm"
include "adantl.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem dipassr2
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cU: class U
  let cX: class X
  assume ipass.1: |- X = ( BaseSet ` U )
  assume ipass.4: |- S = ( .sOLD ` U )
  assume ipass.7: |- P = ( .iOLD ` U )


  assert |- ( ( U e. CPreHilOLD /\ ( A e. X /\ B e. CC /\ C e. X ) ) -> ( A P ( ( * ` B ) S C ) ) = ( B x. ( A P C ) ) )

  proof
    cU
    ccphlo
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cB
    ccj
    cfv
    #
    cC
    cS
    co
    cP
    co
    #
    @6
    ccj
    cfv
    #
    cA
    cC
    cP
    co
    #
    cmul
    co
    #
    cB
    @9
    cmul
    co
    @2
    @1
    @0
    @6
    cc
    wcel
    @3
    @7
    @10
    wceq
    cB
    cjcl
    cA
    @6
    cC
    cP
    cS
    cU
    cX
    ipass.1
    ipass.4
    ipass.7
    dipassr
    syl3anr2
    @5
    @8
    cB
    @9
    cmul
    @4
    @8
    cB
    wceq
    #
    @0
    @2
    @1
    @11
    @3
    cB
    cjcj
    3ad2ant2
    adantl
    oveq1d
    eqtrd
end
