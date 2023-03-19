include "wxo.mm"
include "wb.mm"
include "df-xor.mm"
include "con2bii.mm"

theorem xnor
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ps ) <-> -. ( ph \/_ ps ) )

  proof
    wph
    wps
    wxo
    wph
    wps
    wb
    wph
    wps
    df-xor
    con2bii
end
