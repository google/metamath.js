include "wa.mm"
include "wal.mm"
include "nfrdOLD.mm"
include "imdistani.mm"
include "19.28OLD.mm"
include "sylibr.mm"
include "nfiOLD.mm"

theorem nfan1OLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nfan1OLD.1: |- nfOLD x ph
  assume nfan1OLD.2: |- ( ph -> nfOLD x ps )


  assert |- nfOLD x ( ph /\ ps )

  proof
    wph
    wps
    wa
    #
    vx
    @0
    wph
    wps
    vx
    wal
    #
    wa
    @0
    vx
    wal
    wph
    wps
    @1
    wph
    wps
    vx
    nfan1OLD.2
    nfrdOLD
    imdistani
    wph
    wps
    vx
    nfan1OLD.1
    19.28OLD
    sylibr
    nfiOLD
end
