include "wal.mm"
include "wi.mm"
include "wn.mm"
include "wex.mm"
include "df-ex.mm"
include "19.9ht.mm"
include "syl5bir.mm"
include "con1d.mm"

theorem hbntOLD
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x ( ph -> A. x ph ) -> ( -. ph -> A. x -. ph ) )

  proof
    wph
    wph
    vx
    wal
    wi
    vx
    wal
    #
    wph
    wn
    vx
    wal
    #
    wph
    @1
    wn
    wph
    vx
    wex
    @0
    wph
    wph
    vx
    df-ex
    wph
    vx
    19.9ht
    syl5bir
    con1d
end
