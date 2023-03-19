include "wssb.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "df-ssb.mm"
include "ax6ev.mm"
include "exim.mm"
include "mpi.mm"
include "sylbi.mm"
include "eximi.mm"
include "pm2.27.mm"
include "ax-mp.mm"
include "exlimiv.mm"
include "3syl.mm"

theorem bj-sbex
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let vy: setvar y


  assert |- ( [b t /b x ]b ph -> E. x ph )

  proof
    wph
    vx
    vt
    wssb
    #
    vx
    vy
    weq
    #
    wph
    wi
    vx
    wal
    #
    vy
    wex
    #
    @1
    vx
    wex
    #
    wph
    vx
    wex
    #
    wi
    #
    vy
    wex
    @5
    @0
    vy
    vt
    weq
    #
    @2
    wi
    vy
    wal
    #
    @3
    wph
    vx
    vy
    vt
    df-ssb
    @8
    @7
    vy
    wex
    @3
    vy
    vt
    ax6ev
    @7
    @2
    vy
    exim
    mpi
    sylbi
    @2
    @6
    vy
    @1
    wph
    vx
    exim
    eximi
    @6
    @5
    vy
    @4
    @6
    @5
    wi
    vx
    vy
    ax6ev
    @4
    @5
    pm2.27
    ax-mp
    exlimiv
    3syl
end
