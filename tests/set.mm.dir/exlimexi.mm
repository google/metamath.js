include "wex.mm"
include "hbe1.mm"
include "exlimdh.mm"
include "pm2.43i.mm"

theorem exlimexi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume exlimexi.1: |- ( ps -> A. x ps )
  assume exlimexi.2: |- ( E. x ph -> ( ph -> ps ) )


  assert |- ( E. x ph -> ps )

  proof
    wph
    vx
    wex
    #
    wps
    @0
    wph
    wps
    vx
    wph
    vx
    hbe1
    exlimexi.1
    exlimexi.2
    exlimdh
    pm2.43i
end
