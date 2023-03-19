include "weu.mm"
include "cio.mm"
include "cvv.mm"
include "wcel.mm"
include "wal.mm"
include "wsbc.mm"
include "wi.mm"
include "iotaexeu.mm"
include "spsbc.mm"
include "syl.mm"

theorem pm14.18
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( E! x ph -> ( A. x ps -> [. ( iota x ph ) / x ]. ps ) )

  proof
    wph
    vx
    weu
    wph
    vx
    cio
    #
    cvv
    wcel
    wps
    vx
    wal
    wps
    vx
    @0
    wsbc
    wi
    wph
    vx
    iotaexeu
    wps
    vx
    @0
    cvv
    spsbc
    syl
end
