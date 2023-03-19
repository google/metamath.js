include "cph.mm"
include "co.mm"
include "chj.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "3oalem4.mm"
include "cin.mm"
include "cch.mm"
include "choccli.mm"
include "chjcli.mm"
include "chincli.mm"
include "eqeltri.mm"
include "osumi.mm"
include "ax-mp.mm"
include "chshii.mm"
include "shscomi.mm"
include "chjcomi.mm"
include "3eqtr4i.mm"
include "ineq12i.mm"

theorem 3oalem5
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  assume 3oa.1: |- A e. CH
  assume 3oa.2: |- B e. CH
  assume 3oa.3: |- C e. CH
  assume 3oa.4: |- R = ( ( _|_ ` B ) i^i ( B vH A ) )
  assume 3oa.5: |- S = ( ( _|_ ` C ) i^i ( C vH A ) )


  assert |- ( ( B +H R ) i^i ( C +H S ) ) = ( ( B vH R ) i^i ( C vH S ) )

  proof
    cB
    cR
    cph
    co
    #
    cB
    cR
    chj
    co
    #
    cC
    cS
    cph
    co
    #
    cC
    cS
    chj
    co
    #
    cR
    cB
    cph
    co
    #
    cR
    cB
    chj
    co
    #
    @0
    @1
    cR
    cB
    cort
    cfv
    #
    wss
    @4
    @5
    wceq
    cA
    cB
    cR
    3oa.4
    3oalem4
    cR
    cB
    cR
    @6
    cB
    cA
    chj
    co
    #
    cin
    cch
    3oa.4
    @6
    @7
    cB
    3oa.2
    choccli
    cB
    cA
    3oa.2
    3oa.1
    chjcli
    chincli
    eqeltri
    #
    3oa.2
    osumi
    ax-mp
    cB
    cR
    cB
    3oa.2
    chshii
    cR
    @8
    chshii
    shscomi
    cB
    cR
    3oa.2
    @8
    chjcomi
    3eqtr4i
    cS
    cC
    cph
    co
    #
    cS
    cC
    chj
    co
    #
    @2
    @3
    cS
    cC
    cort
    cfv
    #
    wss
    @9
    @10
    wceq
    cA
    cC
    cS
    3oa.5
    3oalem4
    cS
    cC
    cS
    @11
    cC
    cA
    chj
    co
    #
    cin
    cch
    3oa.5
    @11
    @12
    cC
    3oa.3
    choccli
    cC
    cA
    3oa.3
    3oa.1
    chjcli
    chincli
    eqeltri
    #
    3oa.3
    osumi
    ax-mp
    cC
    cS
    cC
    3oa.3
    chshii
    cS
    @13
    chshii
    shscomi
    cC
    cS
    3oa.3
    @13
    chjcomi
    3eqtr4i
    ineq12i
end
