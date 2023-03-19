include "nfiOLD.mm"
include "exlimdOLD.mm"

theorem exlimdhOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume exlimdhOLD.1: |- ( ph -> A. x ph )
  assume exlimdhOLD.2: |- ( ch -> A. x ch )
  assume exlimdhOLD.3: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( E. x ps -> ch ) )

  proof
    wph
    wps
    wch
    vx
    wph
    vx
    exlimdhOLD.1
    nfiOLD
    wch
    vx
    exlimdhOLD.2
    nfiOLD
    exlimdhOLD.3
    exlimdOLD
end
