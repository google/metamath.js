include "wb.mm"
include "wn.mm"
include "wxo.mm"
include "bicom.mm"
include "notbii.mm"
include "df-xor.mm"
include "3bitr4i.mm"

theorem xorcom
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph \/_ ps ) <-> ( ps \/_ ph ) )

  proof
    wph
    wps
    wb
    #
    wn
    wps
    wph
    wb
    #
    wn
    wph
    wps
    wxo
    wps
    wph
    wxo
    @0
    @1
    wph
    wps
    bicom
    notbii
    wph
    wps
    df-xor
    wps
    wph
    df-xor
    3bitr4i
end
