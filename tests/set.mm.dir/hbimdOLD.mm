include "wi.mm"
include "nfdhOLD.mm"
include "nfimdOLD.mm"
include "nfrdOLD.mm"

theorem hbimdOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume hbimdOLD.1: |- ( ph -> A. x ph )
  assume hbimdOLD.2: |- ( ph -> ( ps -> A. x ps ) )
  assume hbimdOLD.3: |- ( ph -> ( ch -> A. x ch ) )


  assert |- ( ph -> ( ( ps -> ch ) -> A. x ( ps -> ch ) ) )

  proof
    wph
    wps
    wch
    wi
    vx
    wph
    wps
    wch
    vx
    wph
    wps
    vx
    hbimdOLD.1
    hbimdOLD.2
    nfdhOLD
    wph
    wch
    vx
    hbimdOLD.1
    hbimdOLD.3
    nfdhOLD
    nfimdOLD
    nfrdOLD
end
