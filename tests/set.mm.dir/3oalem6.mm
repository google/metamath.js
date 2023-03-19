include "cph.mm"
include "co.mm"
include "cin.mm"
include "chj.mm"
include "chshii.mm"
include "cort.mm"
include "cfv.mm"
include "cch.mm"
include "choccli.mm"
include "chjcli.mm"
include "chincli.mm"
include "eqeltri.mm"
include "shscli.mm"
include "shincli.mm"
include "shsleji.mm"
include "wss.mm"
include "chsleji.mm"
include "ssrin.mm"
include "ax-mp.mm"
include "sslin.mm"
include "sstri.mm"
include "shlej2i.mm"

theorem 3oalem6
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


  assert |- ( B +H ( R i^i ( S +H ( ( B +H C ) i^i ( R +H S ) ) ) ) ) C_ ( B vH ( R i^i ( S vH ( ( B vH C ) i^i ( R vH S ) ) ) ) )

  proof
    cB
    cR
    cS
    cB
    cC
    cph
    co
    #
    cR
    cS
    cph
    co
    #
    cin
    #
    cph
    co
    #
    cin
    #
    cph
    co
    cB
    @4
    chj
    co
    #
    cB
    cR
    cS
    cB
    cC
    chj
    co
    #
    cR
    cS
    chj
    co
    #
    cin
    #
    chj
    co
    #
    cin
    #
    chj
    co
    #
    cB
    @4
    cB
    3oa.2
    chshii
    #
    cR
    @3
    cR
    cR
    cB
    cort
    cfv
    #
    cB
    cA
    chj
    co
    #
    cin
    cch
    3oa.4
    @13
    @14
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
    chshii
    #
    cS
    @2
    cS
    cS
    cC
    cort
    cfv
    #
    cC
    cA
    chj
    co
    #
    cin
    cch
    3oa.5
    @17
    @18
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
    chshii
    #
    @0
    @1
    cB
    cC
    @12
    cC
    3oa.3
    chshii
    shscli
    cR
    cS
    @16
    @20
    shscli
    shincli
    #
    shscli
    shincli
    #
    shsleji
    @4
    @10
    wss
    #
    @5
    @11
    wss
    @3
    @9
    wss
    @23
    @3
    cS
    @2
    chj
    co
    #
    @9
    cS
    @2
    @20
    @21
    shsleji
    @2
    @8
    wss
    @24
    @9
    wss
    @2
    @6
    @1
    cin
    #
    @8
    @0
    @6
    wss
    @2
    @25
    wss
    cB
    cC
    3oa.2
    3oa.3
    chsleji
    @0
    @6
    @1
    ssrin
    ax-mp
    @1
    @7
    wss
    @25
    @8
    wss
    cR
    cS
    @15
    @19
    chsleji
    @1
    @7
    @6
    sslin
    ax-mp
    sstri
    @2
    @8
    cS
    @21
    @8
    @6
    @7
    cB
    cC
    3oa.2
    3oa.3
    chjcli
    cR
    cS
    @15
    @19
    chjcli
    chincli
    #
    chshii
    @20
    shlej2i
    ax-mp
    sstri
    @3
    @9
    cR
    sslin
    ax-mp
    @4
    @10
    cB
    @22
    @10
    cR
    @9
    @15
    cS
    @8
    @19
    @26
    chjcli
    chincli
    chshii
    @12
    shlej2i
    ax-mp
    sstri
end
