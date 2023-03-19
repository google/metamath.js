include "wsb.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "bj-sb4v.mm"
include "bj-sb2v.mm"
include "axc4i.mm"
include "syl.mm"

theorem bj-hbs1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( [ y / x ] ph -> A. x [ y / x ] ph )

  proof
    wph
    vx
    vy
    wsb
    #
    vx
    vy
    weq
    wph
    wi
    #
    vx
    wal
    @0
    vx
    wal
    wph
    vx
    vy
    bj-sb4v
    @1
    @0
    vx
    wph
    vx
    vy
    bj-sb2v
    axc4i
    syl
end
