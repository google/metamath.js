include "wal.mm"
include "wi.mm"
include "wnfOLD.mm"
include "albidOLD.mm"
include "imbi12d.mm"
include "df-nfOLD.mm"
include "3bitr4g.mm"

theorem nfbidfOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume nfbidfOLD.1: |- nfOLD x ph
  assume nfbidfOLD.2: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( nfOLD x ps <-> nfOLD x ch ) )

  proof
    wph
    wps
    wps
    vx
    wal
    #
    wi
    #
    vx
    wal
    wch
    wch
    vx
    wal
    #
    wi
    #
    vx
    wal
    wps
    vx
    wnfOLD
    wch
    vx
    wnfOLD
    wph
    @1
    @3
    vx
    nfbidfOLD.1
    wph
    wps
    wch
    @0
    @2
    nfbidfOLD.2
    wph
    wps
    wch
    vx
    nfbidfOLD.1
    nfbidfOLD.2
    albidOLD
    imbi12d
    albidOLD
    wps
    vx
    df-nfOLD
    wch
    vx
    df-nfOLD
    3bitr4g
end
