include "wal.mm"
include "wi.mm"
include "bj-imim21.mm"

theorem bj-axc4
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( A. x ph -> A. x A. x ph ) -> ( ( A. x ( A. x ph -> ps ) -> ( A. x A. x ph -> A. x ps ) ) -> ( A. x ( A. x ph -> ps ) -> ( A. x ph -> A. x ps ) ) ) )

  proof
    wph
    vx
    wal
    #
    @0
    vx
    wal
    @0
    wps
    wi
    vx
    wal
    wps
    vx
    wal
    bj-imim21
end
