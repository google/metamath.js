include "weq.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "bj-ax12.mm"
include "pm3.31.mm"
include "aleximi.mm"
include "ax-mp.mm"
include "bj-modal5e.mm"
include "syl.mm"
include "equs4v.mm"
include "impbii.mm"

theorem bj-sb56
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

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
    #
    vx
    wal
    #
    @2
    @4
    vx
    wex
    #
    @4
    @0
    wph
    @4
    wi
    wi
    #
    vx
    wal
    @2
    @5
    wi
    wph
    vx
    vy
    bj-ax12
    @6
    @1
    @4
    vx
    @0
    wph
    @4
    pm3.31
    aleximi
    ax-mp
    @3
    vx
    bj-modal5e
    syl
    wph
    vx
    vy
    equs4v
    impbii
end
