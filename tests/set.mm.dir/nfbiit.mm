include "wb.mm"
include "wal.mm"
include "wex.mm"
include "wi.mm"
include "wnf.mm"
include "exbi.mm"
include "albi.mm"
include "imbi12d.mm"
include "df-nf.mm"
include "3bitr4g.mm"

theorem nfbiit
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x


  assert |- ( A. x ( ph <-> ps ) -> ( F/ x ph <-> F/ x ps ) )

  proof
    wph
    wps
    wb
    vx
    wal
    #
    wph
    vx
    wex
    #
    wph
    vx
    wal
    #
    wi
    wps
    vx
    wex
    #
    wps
    vx
    wal
    #
    wi
    wph
    vx
    wnf
    wps
    vx
    wnf
    @0
    @1
    @3
    @2
    @4
    wph
    wps
    vx
    exbi
    wph
    wps
    vx
    albi
    imbi12d
    wph
    vx
    df-nf
    wps
    vx
    df-nf
    3bitr4g
end
