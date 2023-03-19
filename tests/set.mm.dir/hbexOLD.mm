include "wex.mm"
include "wn.mm"
include "wal.mm"
include "df-ex.mm"
include "hbn.mm"
include "hbal.mm"
include "hbxfrbi.mm"

theorem hbexOLD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume hbexOLD.1: |- ( ph -> A. x ph )


  assert |- ( E. y ph -> A. x E. y ph )

  proof
    wph
    vy
    wex
    wph
    wn
    #
    vy
    wal
    #
    wn
    vx
    wph
    vy
    df-ex
    @1
    vx
    @0
    vx
    vy
    wph
    vx
    hbexOLD.1
    hbn
    hbal
    hbn
    hbxfrbi
end
