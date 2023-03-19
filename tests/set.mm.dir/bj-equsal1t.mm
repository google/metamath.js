include "wnf.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "bj-alequex.mm"
include "19.9t.mm"
include "syl5ib.mm"
include "nf5r.mm"
include "ala1.mm"
include "syl6.mm"
include "impbid.mm"

theorem bj-equsal1t
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( F/ x ph -> ( A. x ( x = y -> ph ) <-> ph ) )

  proof
    wph
    vx
    wnf
    #
    vx
    vy
    weq
    #
    wph
    wi
    vx
    wal
    #
    wph
    @2
    wph
    vx
    wex
    @0
    wph
    wph
    vx
    vy
    bj-alequex
    wph
    vx
    19.9t
    syl5ib
    @0
    wph
    wph
    vx
    wal
    @2
    wph
    vx
    nf5r
    wph
    @1
    vx
    ala1
    syl6
    impbid
end
