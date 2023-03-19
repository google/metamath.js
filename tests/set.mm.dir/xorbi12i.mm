include "wb.mm"
include "wn.mm"
include "wxo.mm"
include "bibi12i.mm"
include "notbii.mm"
include "df-xor.mm"
include "3bitr4i.mm"

theorem xorbi12i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume xorbi12.1: |- ( ph <-> ps )
  assume xorbi12.2: |- ( ch <-> th )


  assert |- ( ( ph \/_ ch ) <-> ( ps \/_ th ) )

  proof
    wph
    wch
    wb
    #
    wn
    wps
    wth
    wb
    #
    wn
    wph
    wch
    wxo
    wps
    wth
    wxo
    @0
    @1
    wph
    wps
    wch
    wth
    xorbi12.1
    xorbi12.2
    bibi12i
    notbii
    wph
    wch
    df-xor
    wps
    wth
    df-xor
    3bitr4i
end
