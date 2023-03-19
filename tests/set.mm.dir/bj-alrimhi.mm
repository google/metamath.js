include "wnf.mm"
include "wex.mm"
include "wal.mm"
include "wi.mm"
include "df-nf.mm"
include "biimpi.mm"
include "alimi.mm"
include "syl6.mm"

theorem bj-alrimhi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume bj-alrimhi.1: |- ( ph -> ps )


  assert |- ( F/ x ph -> ( E. x ph -> A. x ps ) )

  proof
    wph
    vx
    wnf
    #
    wph
    vx
    wex
    #
    wph
    vx
    wal
    #
    wps
    vx
    wal
    @0
    @1
    @2
    wi
    wph
    vx
    df-nf
    biimpi
    wph
    wps
    vx
    bj-alrimhi.1
    alimi
    syl6
end
