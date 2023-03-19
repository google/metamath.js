include "chj.mm"
include "co.mm"
include "cin.mm"
include "cph.mm"
include "3oalem5.mm"
include "cort.mm"
include "cfv.mm"
include "cch.mm"
include "choccli.mm"
include "chjcli.mm"
include "chincli.mm"
include "eqeltri.mm"
include "3oalem3.mm"
include "3oalem6.mm"
include "sstri.mm"
include "eqsstr3i.mm"

theorem 3oai
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


  assert |- ( ( B vH R ) i^i ( C vH S ) ) C_ ( B vH ( R i^i ( S vH ( ( B vH C ) i^i ( R vH S ) ) ) ) )

  proof
    cB
    cR
    chj
    co
    cC
    cS
    chj
    co
    cin
    cB
    cR
    cph
    co
    cC
    cS
    cph
    co
    cin
    #
    cB
    cR
    cS
    cB
    cC
    chj
    co
    cR
    cS
    chj
    co
    cin
    chj
    co
    cin
    chj
    co
    #
    cA
    cB
    cC
    cR
    cS
    3oa.1
    3oa.2
    3oa.3
    3oa.4
    3oa.5
    3oalem5
    @0
    cB
    cR
    cS
    cB
    cC
    cph
    co
    cR
    cS
    cph
    co
    cin
    cph
    co
    cin
    cph
    co
    @1
    cB
    cC
    cR
    cS
    3oa.2
    3oa.3
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
    @2
    @3
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
    @4
    @5
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
    3oalem3
    cA
    cB
    cC
    cR
    cS
    3oa.1
    3oa.2
    3oa.3
    3oa.4
    3oa.5
    3oalem6
    sstri
    eqsstr3i
end
