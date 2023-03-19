include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wo.mm"
include "nfn.mm"
include "19.21.mm"
include "df-or.mm"
include "albii.mm"
include "3bitr4i.mm"

theorem 19.32
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.32.1: |- F/ x ph


  assert |- ( A. x ( ph \/ ps ) <-> ( ph \/ A. x ps ) )

  proof
    wph
    wn
    #
    wps
    wi
    #
    vx
    wal
    @0
    wps
    vx
    wal
    #
    wi
    wph
    wps
    wo
    #
    vx
    wal
    wph
    @2
    wo
    @0
    wps
    vx
    wph
    vx
    19.32.1
    nfn
    19.21
    @3
    @1
    vx
    wph
    wps
    df-or
    albii
    wph
    @2
    df-or
    3bitr4i
end
