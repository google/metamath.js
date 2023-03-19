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
include "equs4.mm"
include "impbii.mm"

theorem equs45f
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume equs45f.1: |- F/ y ph


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
    equs45f.1
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
    equs4
    impbii
end
