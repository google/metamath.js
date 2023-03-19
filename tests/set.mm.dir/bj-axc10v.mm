include "weq.mm"
include "wal.mm"
include "wi.mm"
include "wn.mm"
include "ax6v.mm"
include "con3.mm"
include "al2imi.mm"
include "mtoi.mm"
include "axc7.mm"
include "syl.mm"

theorem bj-axc10v
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( A. x ( x = y -> A. x ph ) -> ph )

  proof
    vx
    vy
    weq
    #
    wph
    vx
    wal
    #
    wi
    #
    vx
    wal
    #
    @1
    wn
    #
    vx
    wal
    #
    wn
    wph
    @3
    @5
    @0
    wn
    #
    vx
    wal
    vx
    vy
    ax6v
    @2
    @4
    @6
    vx
    @0
    @1
    con3
    al2imi
    mtoi
    wph
    vx
    axc7
    syl
end
