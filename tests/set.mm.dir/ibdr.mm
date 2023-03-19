include "bicomdd.mm"
include "ibd.mm"

theorem ibdr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume ibdr.1: |- ( ph -> ( ch -> ( ps <-> ch ) ) )


  assert |- ( ph -> ( ch -> ps ) )

  proof
    wph
    wch
    wps
    wph
    wch
    wps
    wch
    ibdr.1
    bicomdd
    ibd
end
