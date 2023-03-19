include "weu.mm"
include "wsb.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "nfv.mm"
include "eu1.mm"
include "exsimpl.mm"
include "sylbi.mm"

theorem euexALT
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( E! x ph -> E. x ph )

  proof
    wph
    vx
    weu
    wph
    wph
    vx
    vy
    wsb
    vx
    vy
    weq
    wi
    vy
    wal
    #
    wa
    vx
    wex
    wph
    vx
    wex
    wph
    vx
    vy
    wph
    vy
    nfv
    eu1
    wph
    @0
    vx
    exsimpl
    sylbi
end
