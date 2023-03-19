include "wb.mm"
include "cio.mm"
include "wceq.mm"
include "iotabi.mm"
include "mpg.mm"

theorem iotabii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume iotabii.1: |- ( ph <-> ps )


  assert |- ( iota x ph ) = ( iota x ps )

  proof
    wph
    wps
    wb
    wph
    vx
    cio
    wps
    vx
    cio
    wceq
    vx
    wph
    wps
    vx
    iotabi
    iotabii.1
    mpg
end
