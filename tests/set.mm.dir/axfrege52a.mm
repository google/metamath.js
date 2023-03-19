include "wb.mm"
include "wif.mm"
include "ifpbi1.mm"
include "biimpd.mm"

theorem axfrege52a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph <-> ps ) -> ( if- ( ph , th , ch ) -> if- ( ps , th , ch ) ) )

  proof
    wph
    wps
    wb
    wph
    wth
    wch
    wif
    wps
    wth
    wch
    wif
    wph
    wps
    wth
    wch
    ifpbi1
    biimpd
end
