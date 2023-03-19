include "wnf.mm"
include "wsb.mm"
include "wex.mm"
include "spsbe.mm"
include "19.9t.mm"
include "syl5ib.mm"
include "wal.mm"
include "nf5r.mm"
include "bj-stdpc4v.mm"
include "syl6.mm"
include "impbid.mm"

theorem bj-sbftv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( F/ x ph -> ( [ y / x ] ph <-> ph ) )

  proof
    wph
    vx
    wnf
    #
    wph
    vx
    vy
    wsb
    #
    wph
    @1
    wph
    vx
    wex
    @0
    wph
    wph
    vx
    vy
    spsbe
    wph
    vx
    19.9t
    syl5ib
    @0
    wph
    wph
    vx
    wal
    @1
    wph
    vx
    nf5r
    wph
    vx
    vy
    bj-stdpc4v
    syl6
    impbid
end
