include "wi.mm"
include "wal.mm"
include "ax-c4.mm"
include "ax-c5.mm"
include "syl5.mm"
include "mpg.mm"
include "syl.mm"

theorem ax4fromc4
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) )

  proof
    wph
    wps
    wi
    #
    vx
    wal
    #
    wph
    vx
    wal
    #
    wps
    wi
    #
    vx
    wal
    #
    @2
    wps
    vx
    wal
    wi
    @1
    @3
    wi
    @1
    @4
    wi
    vx
    @0
    @3
    vx
    ax-c4
    @2
    wph
    @1
    wps
    wph
    vx
    ax-c5
    @0
    vx
    ax-c5
    syl5
    mpg
    wph
    wps
    vx
    ax-c4
    syl
end
