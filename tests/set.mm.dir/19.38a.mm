include "wnf.mm"
include "wex.mm"
include "wal.mm"
include "wi.mm"
include "19.38.mm"
include "df-nf.mm"
include "alim.mm"
include "imim1.mm"
include "syl5.mm"
include "sylbi.mm"
include "impbid2.mm"

theorem 19.38a
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( F/ x ph -> ( ( E. x ph -> A. x ps ) <-> A. x ( ph -> ps ) ) )

  proof
    wph
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
    @1
    wph
    vx
    wal
    #
    wi
    #
    @4
    @3
    wi
    wph
    vx
    df-nf
    @4
    @5
    @2
    wi
    @6
    @3
    wph
    wps
    vx
    alim
    @1
    @5
    @2
    imim1
    syl5
    sylbi
    impbid2
end
