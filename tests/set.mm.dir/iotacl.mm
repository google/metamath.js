include "weu.mm"
include "cio.mm"
include "wsbc.mm"
include "cab.mm"
include "wcel.mm"
include "iota4.mm"
include "df-sbc.mm"
include "sylib.mm"

theorem iotacl
  let wph: wff ph
  let vx: setvar x


  assert |- ( E! x ph -> ( iota x ph ) e. { x | ph } )

  proof
    wph
    vx
    weu
    wph
    vx
    wph
    vx
    cio
    #
    wsbc
    @0
    wph
    vx
    cab
    wcel
    wph
    vx
    iota4
    wph
    vx
    @0
    df-sbc
    sylib
end
