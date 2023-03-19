include "wal.mm"
include "wi.mm"
include "wnfOLD.mm"
include "alrimiOLD.mm"
include "df-nfOLD.mm"
include "sylibr.mm"

theorem nfdOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nfdOLD.1: |- nfOLD x ph
  assume nfdOLD.2: |- ( ph -> ( ps -> A. x ps ) )


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
    nfdOLD.1
    nfdOLD.2
    alrimiOLD
    wps
    vx
    df-nfOLD
    sylibr
end
