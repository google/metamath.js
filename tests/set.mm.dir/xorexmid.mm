include "wn.mm"
include "wxo.mm"
include "wb.mm"
include "pm5.19.mm"
include "df-xor.mm"
include "mpbir.mm"

theorem xorexmid
  let wph: wff ph


  assert |- ( ph \/_ -. ph )

  proof
    wph
    wph
    wn
    #
    wxo
    wph
    @0
    wb
    wn
    wph
    pm5.19
    wph
    @0
    df-xor
    mpbir
end
