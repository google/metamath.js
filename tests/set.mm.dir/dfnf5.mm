include "wex.mm"
include "wal.mm"
include "wi.mm"
include "wn.mm"
include "wo.mm"
include "wnf.mm"
include "cab.mm"
include "c0.mm"
include "wceq.mm"
include "cvv.mm"
include "df-ex.mm"
include "imbi1i.mm"
include "pm4.64.mm"
include "bitri.mm"
include "df-nf.mm"
include "ab0.mm"
include "abv.mm"
include "orbi12i.mm"
include "3bitr4i.mm"

theorem dfnf5
  let wph: wff ph
  let vx: setvar x


  assert |- ( F/ x ph <-> ( { x | ph } = (/) \/ { x | ph } = _V ) )

  proof
    wph
    vx
    wex
    #
    wph
    vx
    wal
    #
    wi
    #
    wph
    wn
    vx
    wal
    #
    @1
    wo
    #
    wph
    vx
    wnf
    wph
    vx
    cab
    #
    c0
    wceq
    #
    @5
    cvv
    wceq
    #
    wo
    @2
    @3
    wn
    #
    @1
    wi
    @4
    @0
    @8
    @1
    wph
    vx
    df-ex
    imbi1i
    @3
    @1
    pm4.64
    bitri
    wph
    vx
    df-nf
    @6
    @3
    @7
    @1
    wph
    vx
    ab0
    wph
    vx
    abv
    orbi12i
    3bitr4i
end
