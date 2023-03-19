include "wnf.mm"
include "wn.mm"
include "wex.mm"
include "wal.mm"
include "wb.mm"
include "nfnt.mm"
include "19.9t.mm"
include "syl.mm"
include "con2bid.mm"
include "alex.mm"
include "syl6rbbr.mm"

theorem 19.9alt
  let wph: wff ph
  let vx: setvar x


  assert |- ( F/ x ph -> ( A. x ph <-> ph ) )

  proof
    wph
    vx
    wnf
    #
    wph
    wph
    wn
    #
    vx
    wex
    #
    wn
    wph
    vx
    wal
    @0
    @2
    wph
    @0
    @1
    vx
    wnf
    @2
    @1
    wb
    wph
    vx
    nfnt
    @1
    vx
    19.9t
    syl
    con2bid
    wph
    vx
    alex
    syl6rbbr
end
