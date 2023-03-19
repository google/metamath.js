include "wal.mm"
include "wi.mm"
include "wnf.mm"
include "alim.mm"
include "nf5.mm"
include "syl6ibr.mm"

theorem bj-nfdt0
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( ph -> ( ps -> A. x ps ) ) -> ( A. x ph -> F/ x ps ) )

  proof
    wph
    wps
    wps
    vx
    wal
    wi
    #
    wi
    vx
    wal
    wph
    vx
    wal
    @0
    vx
    wal
    wps
    vx
    wnf
    wph
    @0
    vx
    alim
    wps
    vx
    nf5
    syl6ibr
end
