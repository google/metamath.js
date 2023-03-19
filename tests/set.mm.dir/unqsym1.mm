include "wfal.mm"
include "weu.mm"
include "wex.mm"
include "unnf.mm"
include "nex.mm"
include "euex.mm"
include "mto.mm"
include "pm2.21i.mm"

theorem unqsym1
  let wph: wff ph
  let vx: setvar x


  assert |- ( E! x E! x F. -> E! x ph )

  proof
    wfal
    vx
    weu
    #
    vx
    weu
    #
    wph
    vx
    weu
    @1
    @0
    vx
    wex
    @0
    vx
    vx
    unnf
    nex
    @0
    vx
    euex
    mto
    pm2.21i
end
