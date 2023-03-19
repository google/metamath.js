include "wxo.mm"
include "wb.mm"
include "wn.mm"
include "notnoti.mm"
include "df-xor.mm"
include "mtbir.mm"

theorem aisbnaxb
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume aisbnaxb.1: |- ( ph <-> ps )


  assert |- -. ( ph \/_ ps )

  proof
    wph
    wps
    wxo
    wph
    wps
    wb
    #
    wn
    @0
    aisbnaxb.1
    notnoti
    wph
    wps
    df-xor
    mtbir
end
