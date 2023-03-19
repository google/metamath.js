include "wex.mm"
include "exlimdh.mm"
include "syl5com.mm"
include "pm2.43i.mm"

theorem eexinst11
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume eexinst11.1: |- ( ph -> E. x ps )
  assume eexinst11.2: |- ( ph -> ( ps -> ch ) )
  assume eexinst11.3: |- ( ph -> A. x ph )
  assume eexinst11.4: |- ( ch -> A. x ch )


  assert |- ( ph -> ch )

  proof
    wph
    wch
    wph
    wps
    vx
    wex
    wph
    wch
    eexinst11.1
    wph
    wps
    wch
    vx
    eexinst11.3
    eexinst11.4
    eexinst11.2
    exlimdh
    syl5com
    pm2.43i
end
