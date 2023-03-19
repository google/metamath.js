include "wb.mm"
include "wnan.mm"
include "nanbi12.mm"
include "syl2anc.mm"

theorem nanbi12d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume nanbid.1: |- ( ph -> ( ps <-> ch ) )
  assume nanbi12d.2: |- ( ph -> ( th <-> ta ) )


  assert |- ( ph -> ( ( ps -/\ th ) <-> ( ch -/\ ta ) ) )

  proof
    wph
    wps
    wch
    wb
    wth
    wta
    wb
    wps
    wth
    wnan
    wch
    wta
    wnan
    wb
    nanbid.1
    nanbi12d.2
    wps
    wch
    wth
    wta
    nanbi12
    syl2anc
end
