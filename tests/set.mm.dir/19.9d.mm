include "wex.mm"
include "wal.mm"
include "wnf.mm"
include "wi.mm"
include "df-nf.mm"
include "sylib.mm"
include "sp.mm"
include "syl6.mm"

theorem 19.9d
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.9d.1: |- ( ps -> F/ x ph )


  assert |- ( ps -> ( E. x ph -> ph ) )

  proof
    wps
    wph
    vx
    wex
    #
    wph
    vx
    wal
    #
    wph
    wps
    wph
    vx
    wnf
    @0
    @1
    wi
    19.9d.1
    wph
    vx
    df-nf
    sylib
    wph
    vx
    sp
    syl6
end
