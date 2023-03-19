include "wb.mm"
include "w3a.mm"
include "bicomd.mm"
include "3exp.mm"

theorem 3impexpbicomi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3impexpbicomi.1: |- ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) )


  assert |- ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) )

  proof
    wph
    wps
    wch
    wta
    wth
    wb
    wph
    wps
    wch
    w3a
    wth
    wta
    3impexpbicomi.1
    bicomd
    3exp
end
