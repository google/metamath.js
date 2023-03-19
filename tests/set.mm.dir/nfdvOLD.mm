include "wal.mm"
include "wi.mm"
include "wnfOLD.mm"
include "alrimiv.mm"
include "df-nfOLD.mm"
include "sylibr.mm"

theorem nfdvOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nfdvOLD.1: |- ( ph -> ( ps -> A. x ps ) )

  disjoint ph x
  assert |- ( ph -> nfOLD x ps )

  proof
    wph
    wps
    wps
    vx
    wal
    wi
    #
    vx
    wal
    wps
    vx
    wnfOLD
    wph
    @0
    vx
    nfdvOLD.1
    alrimiv
    wps
    vx
    df-nfOLD
    sylibr
end
