include "wa.mm"
include "biimpi.mm"
include "simprd.mm"

theorem simprbi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume simprbi.1: |- ( ph <-> ( ps /\ ch ) )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    wph
    wps
    wch
    wa
    simprbi.1
    biimpi
    simprd
end
