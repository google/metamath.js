include "wtru.mm"
include "wal.mm"
include "wex.mm"
include "wi.mm"
include "pm2.27.mm"
include "tru.mm"
include "mpg.mm"

theorem bj-axd2d
  let vx: setvar x


  assert |- ( ( A. x T. -> E. x T. ) -> E. x T. )

  proof
    wtru
    wtru
    vx
    wal
    #
    wtru
    vx
    wex
    #
    wi
    @1
    wi
    vx
    @0
    @1
    pm2.27
    tru
    mpg
end
