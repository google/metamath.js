include "biimpri.mm"
include "syl.mm"

theorem sylbir
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume sylbir.1: |- ( ps <-> ph )
  assume sylbir.2: |- ( ps -> ch )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    wps
    wph
    sylbir.1
    biimpri
    sylbir.2
    syl
end
