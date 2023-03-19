include "wal.mm"
include "wi.mm"
include "wex.mm"
include "bj-biexal1.mm"
include "bj-biexal2.mm"
include "bitr4i.mm"

theorem bj-biexal3
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( ph -> A. x ps ) <-> A. x ( E. x ph -> ps ) )

  proof
    wph
    wps
    vx
    wal
    #
    wi
    vx
    wal
    wph
    vx
    wex
    #
    @0
    wi
    @1
    wps
    wi
    vx
    wal
    wph
    wps
    vx
    bj-biexal1
    wph
    wps
    vx
    bj-biexal2
    bitr4i
end
