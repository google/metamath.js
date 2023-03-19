include "wal.mm"
include "wi.mm"
include "wnfOLD.mm"
include "albii.mm"
include "imbi12i.mm"
include "df-nfOLD.mm"
include "3bitr4i.mm"

theorem nfbiiOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nfbiiOLD.1: |- ( ph <-> ps )


  assert |- ( nfOLD x ph <-> nfOLD x ps )

  proof
    wph
    wph
    vx
    wal
    #
    wi
    #
    vx
    wal
    wps
    wps
    vx
    wal
    #
    wi
    #
    vx
    wal
    wph
    vx
    wnfOLD
    wps
    vx
    wnfOLD
    @1
    @3
    vx
    wph
    wps
    @0
    @2
    nfbiiOLD.1
    wph
    wps
    vx
    nfbiiOLD.1
    albii
    imbi12i
    albii
    wph
    vx
    df-nfOLD
    wps
    vx
    df-nfOLD
    3bitr4i
end
