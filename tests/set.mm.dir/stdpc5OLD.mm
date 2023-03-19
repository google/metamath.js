include "wnf.mm"
include "wi.mm"
include "wal.mm"
include "19.21t.mm"
include "biimpd.mm"
include "ax-mp.mm"

theorem stdpc5OLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume stdpc5.1: |- F/ x ph


  assert |- ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) )

  proof
    wph
    vx
    wnf
    #
    wph
    wps
    wi
    vx
    wal
    #
    wph
    wps
    vx
    wal
    wi
    #
    wi
    stdpc5.1
    @0
    @1
    @2
    wph
    wps
    vx
    19.21t
    biimpd
    ax-mp
end
