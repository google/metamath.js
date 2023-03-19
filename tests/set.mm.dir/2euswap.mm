include "wmo.mm"
include "wal.mm"
include "wex.mm"
include "wa.mm"
include "weu.mm"
include "wi.mm"
include "excomim.mm"
include "a1i.mm"
include "2moswap.mm"
include "anim12d.mm"
include "eu5.mm"
include "3imtr4g.mm"

theorem 2euswap
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x E* y ph -> ( E! x E. y ph -> E! y E. x ph ) )

  proof
    wph
    vy
    wmo
    vx
    wal
    #
    wph
    vy
    wex
    #
    vx
    wex
    #
    @1
    vx
    wmo
    #
    wa
    wph
    vx
    wex
    #
    vy
    wex
    #
    @4
    vy
    wmo
    #
    wa
    @1
    vx
    weu
    @4
    vy
    weu
    @0
    @2
    @5
    @3
    @6
    @2
    @5
    wi
    @0
    wph
    vx
    vy
    excomim
    a1i
    wph
    vx
    vy
    2moswap
    anim12d
    @1
    vx
    eu5
    @4
    vy
    eu5
    3imtr4g
end
