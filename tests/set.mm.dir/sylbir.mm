include "biimpri.mm"
include "syl.mm"

theorem sylbir
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
