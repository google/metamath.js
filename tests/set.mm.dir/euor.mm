include "wn.mm"
include "weu.mm"
include "wo.mm"
include "nfn.mm"
include "biorf.mm"
include "eubid.mm"
include "biimpa.mm"

theorem euor
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume euor.1: |- F/ x ph


  assert |- ( ( -. ph /\ E! x ps ) -> E! x ( ph \/ ps ) )

  proof
    wph
    wn
    #
    wps
    vx
    weu
    wph
    wps
    wo
    #
    vx
    weu
    @0
    wps
    @1
    vx
    wph
    vx
    euor.1
    nfn
    wph
    wps
    biorf
    eubid
    biimpa
end
