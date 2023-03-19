include "wn.mm"
include "wal.mm"
include "wex.mm"
include "alcom.mm"
include "notbii.mm"
include "2exnaln.mm"
include "3bitr4i.mm"

theorem excom
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( E. x E. y ph <-> E. y E. x ph )

  proof
    wph
    wn
    #
    vy
    wal
    vx
    wal
    #
    wn
    @0
    vx
    wal
    vy
    wal
    #
    wn
    wph
    vy
    wex
    vx
    wex
    wph
    vx
    wex
    vy
    wex
    @1
    @2
    @0
    vx
    vy
    alcom
    notbii
    wph
    vx
    vy
    2exnaln
    wph
    vy
    vx
    2exnaln
    3bitr4i
end
