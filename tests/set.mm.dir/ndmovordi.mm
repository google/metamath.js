include "wcel.mm"
include "co.mm"
include "wbr.mm"
include "brel.mm"
include "simpld.mm"
include "ndmovrcl.mm"
include "syl.mm"
include "biimprd.mm"
include "mpcom.mm"

theorem ndmovordi
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  assume ndmovordi.2: |- dom F = ( S X. S )
  assume ndmovordi.4: |- R C_ ( S X. S )
  assume ndmovordi.5: |- -. (/) e. S
  assume ndmovordi.6: |- ( C e. S -> ( A R B <-> ( C F A ) R ( C F B ) ) )


  assert |- ( ( C F A ) R ( C F B ) -> A R B )

  proof
    cC
    cS
    wcel
    #
    cC
    cA
    cF
    co
    #
    cC
    cB
    cF
    co
    #
    cR
    wbr
    #
    cA
    cB
    cR
    wbr
    #
    @3
    @1
    cS
    wcel
    #
    @0
    @3
    @5
    @2
    cS
    wcel
    @1
    @2
    cS
    cS
    cR
    ndmovordi.4
    brel
    simpld
    @5
    @0
    cA
    cS
    wcel
    cC
    cA
    cS
    cF
    ndmovordi.2
    ndmovordi.5
    ndmovrcl
    simpld
    syl
    @0
    @4
    @3
    ndmovordi.6
    biimprd
    mpcom
end
