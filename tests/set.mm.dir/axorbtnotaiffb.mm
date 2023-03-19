include "wxo.mm"
include "wb.mm"
include "wn.mm"
include "df-xor.mm"
include "mpbi.mm"

theorem axorbtnotaiffb
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume axorbtnotaiffb.1: |- ( ph \/_ ps )


  assert |- -. ( ph <-> ps )

  proof
    wph
    wps
    wxo
    wph
    wps
    wb
    wn
    axorbtnotaiffb.1
    wph
    wps
    df-xor
    mpbi
end
