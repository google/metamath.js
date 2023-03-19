include "wsb.mm"
include "wex.mm"
include "spsbe.mm"
include "19.9v.mm"
include "sylib.mm"
include "wal.mm"
include "ax-5.mm"
include "bj-stdpc4v.mm"
include "syl.mm"
include "impbii.mm"

theorem bj-sbfvv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  disjoint ph x
  assert |- ( [ y / x ] ph <-> ph )

  proof
    wph
    vx
    vy
    wsb
    #
    wph
    @0
    wph
    vx
    wex
    wph
    wph
    vx
    vy
    spsbe
    wph
    vx
    19.9v
    sylib
    wph
    wph
    vx
    wal
    @0
    wph
    vx
    ax-5
    wph
    vx
    vy
    bj-stdpc4v
    syl
    impbii
end
