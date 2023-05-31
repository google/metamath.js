include "wex.mm"
include "wal.mm"
include "wi.mm"
include "wnf.mm"
include "exbid.mm"
include "albid.mm"
include "imbi12d.mm"
include "df-nf.mm"
include "3bitr4g.mm"

theorem nfbidf
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  assume albid.1: |- F/ x ph
  assume albid.2: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( F/ x ps <-> F/ x ch ) )

  proof
    wph
    wps
    vx
    wex
    #
    wps
    vx
    wal
    #
    wi
    wch
    vx
    wex
    #
    wch
    vx
    wal
    #
    wi
    wps
    vx
    wnf
    wch
    vx
    wnf
    wph
    @0
    @2
    @1
    @3
    wph
    wps
    wch
    vx
    albid.1
    albid.2
    exbid
    wph
    wps
    wch
    vx
    albid.1
    albid.2
    albid
    imbi12d
    wps
    vx
    df-nf
    wch
    vx
    df-nf
    3bitr4g
end
