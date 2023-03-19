include "wb.mm"
include "wn.mm"
include "wxo.mm"
include "bibi12d.mm"
include "notbid.mm"
include "df-xor.mm"
include "3bitr4g.mm"

theorem xorbi12d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume xor12d.1: |- ( ph -> ( ps <-> ch ) )
  assume xor12d.2: |- ( ph -> ( th <-> ta ) )


  assert |- ( ph -> ( ( ps \/_ th ) <-> ( ch \/_ ta ) ) )

  proof
    wph
    wps
    wth
    wb
    #
    wn
    wch
    wta
    wb
    #
    wn
    wps
    wth
    wxo
    wch
    wta
    wxo
    wph
    @0
    @1
    wph
    wps
    wch
    wth
    wta
    xor12d.1
    xor12d.2
    bibi12d
    notbid
    wps
    wth
    df-xor
    wch
    wta
    df-xor
    3bitr4g
end
