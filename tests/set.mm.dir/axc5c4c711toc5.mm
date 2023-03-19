include "wal.mm"
include "wn.mm"
include "cv.mm"
include "wceq.mm"
include "ax6v.mm"
include "wi.mm"
include "pm2.21.mm"
include "ax-1.mm"
include "axc5c4c711.mm"
include "3syl.mm"
include "mtoi.mm"
include "con4i.mm"

theorem axc5c4c711toc5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ph -> ph )

  proof
    wph
    wph
    vx
    wal
    #
    wph
    wn
    #
    @0
    vx
    cv
    vy
    cv
    wceq
    wn
    #
    vx
    wal
    #
    vx
    vy
    ax6v
    @1
    wph
    @0
    @2
    wi
    vx
    wal
    #
    wi
    #
    @4
    vx
    wal
    wn
    vx
    wal
    vx
    wal
    #
    @5
    wi
    @0
    @3
    wi
    wph
    @4
    pm2.21
    @5
    @6
    ax-1
    wph
    @2
    vx
    vx
    axc5c4c711
    3syl
    mtoi
    con4i
end
