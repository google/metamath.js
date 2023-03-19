include "cph.mm"
include "co.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "wceq.mm"
include "wex.mm"
include "wrex.mm"
include "chseli.mm"
include "r2ex.mm"
include "bitri.mm"
include "anbi12i.mm"
include "elin.mm"
include "ee4anv.mm"
include "3bitr4i.mm"
include "3oalem2.mm"
include "exlimivv.mm"
include "sylbi.mm"
include "ssriv.mm"

theorem 3oalem3
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  assume 3oalem1.1: |- B e. CH
  assume 3oalem1.2: |- C e. CH
  assume 3oalem1.3: |- R e. CH
  assume 3oalem1.4: |- S e. CH


  assert |- ( ( B +H R ) i^i ( C +H S ) ) C_ ( B +H ( R i^i ( S +H ( ( B +H C ) i^i ( R +H S ) ) ) ) )

  proof
    vv
    cB
    cR
    cph
    co
    #
    cC
    cS
    cph
    co
    #
    cin
    #
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
    #
    vv
    cv
    #
    @2
    wcel
    #
    vx
    cv
    #
    cB
    wcel
    vy
    cv
    #
    cR
    wcel
    wa
    @4
    @6
    @7
    cva
    co
    wceq
    #
    wa
    #
    vz
    cv
    #
    cC
    wcel
    vw
    cv
    #
    cS
    wcel
    wa
    @4
    @10
    @11
    cva
    co
    wceq
    #
    wa
    #
    wa
    #
    vw
    wex
    vz
    wex
    #
    vy
    wex
    vx
    wex
    #
    @4
    @3
    wcel
    #
    @4
    @0
    wcel
    #
    @4
    @1
    wcel
    #
    wa
    @9
    vy
    wex
    vx
    wex
    #
    @13
    vw
    wex
    vz
    wex
    #
    wa
    @5
    @16
    @18
    @20
    @19
    @21
    @18
    @8
    vy
    cR
    wrex
    vx
    cB
    wrex
    @20
    vx
    vy
    cB
    cR
    @4
    3oalem1.1
    3oalem1.3
    chseli
    @8
    vx
    vy
    cB
    cR
    r2ex
    bitri
    @19
    @12
    vw
    cS
    wrex
    vz
    cC
    wrex
    @21
    vz
    vw
    cC
    cS
    @4
    3oalem1.2
    3oalem1.4
    chseli
    @12
    vz
    vw
    cC
    cS
    r2ex
    bitri
    anbi12i
    @4
    @0
    @1
    elin
    @9
    @13
    vx
    vy
    vz
    vw
    ee4anv
    3bitr4i
    @15
    @17
    vx
    vy
    @14
    @17
    vz
    vw
    vx
    vy
    vz
    vw
    vv
    cB
    cC
    cR
    cS
    3oalem1.1
    3oalem1.2
    3oalem1.3
    3oalem1.4
    3oalem2
    exlimivv
    exlimivv
    sylbi
    ssriv
end
