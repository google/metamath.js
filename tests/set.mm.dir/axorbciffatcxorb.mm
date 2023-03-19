include "wxo.mm"
include "wb.mm"
include "wn.mm"
include "axorbtnotaiffb.mm"
include "xor3.mm"
include "mpbi.mm"
include "aiffnbandciffatnotciffb.mm"
include "df-xor.mm"
include "mpbir.mm"

theorem axorbciffatcxorb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vk: setvar k
  let vx: setvar x
  assume axorbciffatcxorb.1: |- ( ph \/_ ps )
  assume axorbciffatcxorb.2: |- ( ch <-> ph )


  assert |- ( ch \/_ ps )

  proof
    wch
    wps
    wxo
    wch
    wps
    wb
    wn
    wph
    wps
    wch
    wph
    wps
    wb
    wn
    wph
    wps
    wn
    wb
    wph
    wps
    axorbciffatcxorb.1
    axorbtnotaiffb
    wph
    wps
    xor3
    mpbi
    axorbciffatcxorb.2
    aiffnbandciffatnotciffb
    wch
    wps
    df-xor
    mpbir
end
