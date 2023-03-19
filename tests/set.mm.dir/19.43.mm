include "wo.mm"
include "wex.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "df-or.mm"
include "exbii.mm"
include "19.35.mm"
include "alnex.mm"
include "imbi1i.mm"
include "3bitri.mm"
include "bitr4i.mm"

theorem 19.43
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ E. x ps ) )

  proof
    wph
    wps
    wo
    #
    vx
    wex
    #
    wph
    vx
    wex
    #
    wn
    #
    wps
    vx
    wex
    #
    wi
    #
    @2
    @4
    wo
    @1
    wph
    wn
    #
    wps
    wi
    #
    vx
    wex
    @6
    vx
    wal
    #
    @4
    wi
    @5
    @0
    @7
    vx
    wph
    wps
    df-or
    exbii
    @6
    wps
    vx
    19.35
    @8
    @3
    @4
    wph
    vx
    alnex
    imbi1i
    3bitri
    @2
    @4
    df-or
    bitr4i
end
