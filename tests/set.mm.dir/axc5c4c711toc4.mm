include "wal.mm"
include "wi.mm"
include "wn.mm"
include "ax-1.mm"
include "axc5c4c711.mm"
include "3syl.mm"

theorem axc5c4c711toc4
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( A. x ph -> ps ) -> ( A. x ph -> A. x ps ) )

  proof
    wph
    vx
    wal
    #
    wps
    wi
    vx
    wal
    #
    wph
    @1
    wi
    #
    @1
    vx
    wal
    wn
    vx
    wal
    vx
    wal
    #
    @2
    wi
    @0
    wps
    vx
    wal
    wi
    @1
    wph
    ax-1
    @2
    @3
    ax-1
    wph
    wps
    vx
    vx
    axc5c4c711
    3syl
end
