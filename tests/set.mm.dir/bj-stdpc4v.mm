include "wal.mm"
include "weq.mm"
include "wi.mm"
include "wsb.mm"
include "ax-1.mm"
include "alimi.mm"
include "bj-sb2v.mm"
include "syl.mm"

theorem bj-stdpc4v
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( A. x ph -> [ y / x ] ph )

  proof
    wph
    vx
    wal
    vx
    vy
    weq
    #
    wph
    wi
    #
    vx
    wal
    wph
    vx
    vy
    wsb
    wph
    @1
    vx
    wph
    @0
    ax-1
    alimi
    wph
    vx
    vy
    bj-sb2v
    syl
end
