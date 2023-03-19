include "wa.mm"
include "biimpi.mm"
include "simprd.mm"

theorem simprbi
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
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
