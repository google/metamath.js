include "weq.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "nf5ri.mm"
include "anim2i.mm"
include "eximi.mm"
include "equs5a.mm"
include "syl.mm"
include "equs4v.mm"
include "impbii.mm"

theorem bj-equs45fv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume bj-equs45fv.1: |- F/ y ph

  disjoint x y
  assert |- ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) )

  proof
    vx
    vy
    weq
    #
    wph
    wa
    #
    vx
    wex
    #
    @0
    wph
    wi
    vx
    wal
    #
    @2
    @0
    wph
    vy
    wal
    #
    wa
    #
    vx
    wex
    @3
    @1
    @5
    vx
    wph
    @4
    @0
    wph
    vy
    bj-equs45fv.1
    nf5ri
    anim2i
    eximi
    wph
    vx
    vy
    equs5a
    syl
    wph
    vx
    vy
    equs4v
    impbii
end
