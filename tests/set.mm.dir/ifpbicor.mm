include "wb.mm"
include "wn.mm"
include "wif.mm"
include "bicom.mm"
include "ifpdfbi.mm"
include "3bitr3i.mm"

theorem ifpbicor
  let wph: wff ph
  let wps: wff ps


  assert |- ( if- ( ph , ps , -. ps ) <-> if- ( ps , ph , -. ph ) )

  proof
    wph
    wps
    wb
    wps
    wph
    wb
    wph
    wps
    wps
    wn
    wif
    wps
    wph
    wph
    wn
    wif
    wph
    wps
    bicom
    wph
    wps
    ifpdfbi
    wps
    wph
    ifpdfbi
    3bitr3i
end
