include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "co.mm"
include "wb.mm"
include "wi.mm"
include "3expia.mm"
include "wn.mm"
include "brel.mm"
include "ndmovrcl.mm"
include "simprd.mm"
include "anim12i.mm"
include "syl.mm"
include "pm5.21ni.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem ndmovord
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  assume ndmov.1: |- dom F = ( S X. S )
  assume ndmovord.4: |- R C_ ( S X. S )
  assume ndmovord.5: |- -. (/) e. S
  assume ndmovord.6: |- ( ( A e. S /\ B e. S /\ C e. S ) -> ( A R B <-> ( C F A ) R ( C F B ) ) )


  assert |- ( C e. S -> ( A R B <-> ( C F A ) R ( C F B ) ) )

  proof
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    wa
    #
    cC
    cS
    wcel
    #
    cA
    cB
    cR
    wbr
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
    wb
    #
    wi
    @0
    @1
    @3
    @8
    ndmovord.6
    3expia
    @2
    wn
    @8
    @3
    @4
    @2
    @7
    cA
    cB
    cS
    cS
    cR
    ndmovord.4
    brel
    @7
    @5
    cS
    wcel
    #
    @6
    cS
    wcel
    #
    wa
    @2
    @5
    @6
    cS
    cS
    cR
    ndmovord.4
    brel
    @9
    @0
    @10
    @1
    @9
    @3
    @0
    cC
    cA
    cS
    cF
    ndmov.1
    ndmovord.5
    ndmovrcl
    simprd
    @10
    @3
    @1
    cC
    cB
    cS
    cF
    ndmov.1
    ndmovord.5
    ndmovrcl
    simprd
    anim12i
    syl
    pm5.21ni
    a1d
    pm2.61i
end
