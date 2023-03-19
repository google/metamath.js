include "wnf.mm"
include "wi.mm"
include "wex.mm"
include "wal.mm"
include "19.35.mm"
include "df-nf.mm"
include "biimpi.mm"
include "imim1d.mm"
include "imim2d.mm"
include "syl9.mm"
include "19.38.mm"
include "syl8.mm"
include "syl7bi.mm"
include "syl6ibr.mm"

theorem nfimt
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( F/ x ph -> ( F/ x ps -> F/ x ( ph -> ps ) ) )

  proof
    wph
    vx
    wnf
    #
    wps
    vx
    wnf
    #
    wph
    wps
    wi
    #
    vx
    wex
    #
    @2
    vx
    wal
    #
    wi
    @2
    vx
    wnf
    @3
    wph
    vx
    wal
    #
    wps
    vx
    wex
    #
    wi
    #
    @0
    @1
    @4
    wph
    wps
    vx
    19.35
    @0
    @1
    @7
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
    @4
    @0
    @7
    @8
    @6
    wi
    @1
    @10
    @0
    @8
    @5
    @6
    @0
    @8
    @5
    wi
    wph
    vx
    df-nf
    biimpi
    imim1d
    @1
    @6
    @9
    @8
    @1
    @6
    @9
    wi
    wps
    vx
    df-nf
    biimpi
    imim2d
    syl9
    wph
    wps
    vx
    19.38
    syl8
    syl7bi
    @2
    vx
    df-nf
    syl6ibr
end
