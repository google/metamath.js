include "wn.mm"
include "wxo.mm"
include "wb.mm"
include "df-xor.mm"
include "pm5.18.mm"
include "xnor.mm"
include "3bitr2i.mm"

theorem xorneg2
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph \/_ -. ps ) <-> -. ( ph \/_ ps ) )

  proof
    wph
    wps
    wn
    #
    wxo
    wph
    @0
    wb
    wn
    wph
    wps
    wb
    wph
    wps
    wxo
    wn
    wph
    @0
    df-xor
    wph
    wps
    pm5.18
    wph
    wps
    xnor
    3bitr2i
end
