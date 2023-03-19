include "wsb.mm"
include "wex.mm"
include "spsbe.mm"
include "eximi.mm"
include "syl.mm"

theorem spsbce-2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( [ z / x ] [ w / y ] ph -> E. x E. y ph )

  proof
    wph
    vy
    vw
    wsb
    #
    vx
    vz
    wsb
    @0
    vx
    wex
    wph
    vy
    wex
    #
    vx
    wex
    @0
    vx
    vz
    spsbe
    @0
    @1
    vx
    wph
    vy
    vw
    spsbe
    eximi
    syl
end
