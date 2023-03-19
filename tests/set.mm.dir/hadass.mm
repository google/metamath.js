include "whad.mm"
include "wxo.mm"
include "df-had.mm"
include "xorass.mm"
include "bitri.mm"

theorem hadass
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( hadd ( ph , ps , ch ) <-> ( ph \/_ ( ps \/_ ch ) ) )

  proof
    wph
    wps
    wch
    whad
    wph
    wps
    wxo
    wch
    wxo
    wph
    wps
    wch
    wxo
    wxo
    wph
    wps
    wch
    df-had
    wph
    wps
    wch
    xorass
    bitri
end
