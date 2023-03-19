include "wb.mm"
include "wnan.mm"
include "nanbi1.mm"
include "syl.mm"

theorem nanbi1d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume nanbid.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( ( ps -/\ th ) <-> ( ch -/\ th ) ) )

  proof
    wph
    wps
    wch
    wb
    wps
    wth
    wnan
    wch
    wth
    wnan
    wb
    nanbid.1
    wps
    wch
    wth
    nanbi1
    syl
end
