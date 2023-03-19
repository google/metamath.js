include "wnf.mm"
include "wex.mm"
include "wal.mm"
include "wi.mm"
include "19.38.mm"
include "df-nf.mm"
include "exim.mm"
include "imim2.mm"
include "syl5.mm"
include "sylbi.mm"
include "impbid2.mm"

theorem 19.38b
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( F/ x ps -> ( ( E. x ph -> A. x ps ) <-> A. x ( ph -> ps ) ) )

  proof
    wps
    vx
    wnf
    #
    wph
    vx
    wex
    #
    wps
    vx
    wal
    #
    wi
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
    19.38
    @0
    wps
    vx
    wex
    #
    @2
    wi
    #
    @4
    @3
    wi
    wps
    vx
    df-nf
    @4
    @1
    @5
    wi
    @6
    @3
    wph
    wps
    vx
    exim
    @5
    @2
    @1
    imim2
    syl5
    sylbi
    impbid2
end
