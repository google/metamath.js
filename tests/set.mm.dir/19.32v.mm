include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wo.mm"
include "19.21v.mm"
include "df-or.mm"
include "albii.mm"
include "3bitr4i.mm"

theorem 19.32v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ph x
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
    19.21v
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
