include "wb.mm"
include "wnan.mm"
include "nanbi2.mm"
include "syl.mm"

theorem nanbi2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume nanbid.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( ( th -/\ ps ) <-> ( th -/\ ch ) ) )

  proof
    wph
    wps
    wch
    wb
    wth
    wps
    wnan
    wth
    wch
    wnan
    wb
    nanbid.1
    wps
    wch
    wth
    nanbi2
    syl
end
