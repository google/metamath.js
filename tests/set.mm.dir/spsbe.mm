include "wsb.mm"
include "weq.mm"
include "wa.mm"
include "wex.mm"
include "sb1.mm"
include "exsimpr.mm"
include "syl.mm"

theorem spsbe
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y


  assert |- ( [ y / x ] ph -> E. x ph )

  proof
    wph
    vx
    vy
    wsb
    vx
    vy
    weq
    #
    wph
    wa
    vx
    wex
    wph
    vx
    wex
    wph
    vx
    vy
    sb1
    @0
    wph
    vx
    exsimpr
    syl
end
