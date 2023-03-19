include "nfriOLD.mm"
include "alimdh.mm"

theorem alimdOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume alimdOLD.1: |- nfOLD x ph
  assume alimdOLD.2: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( A. x ps -> A. x ch ) )

  proof
    wph
    wps
    wch
    vx
    wph
    vx
    alimdOLD.1
    nfriOLD
    alimdOLD.2
    alimdh
end
