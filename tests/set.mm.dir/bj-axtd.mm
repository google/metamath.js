include "wn.mm"
include "wal.mm"
include "wi.mm"
include "wex.mm"
include "con2.mm"
include "df-ex.mm"
include "syl6ibr.mm"
include "imim2d.mm"

theorem bj-axtd
  let wph: wff ph
  let vx: setvar x


  assert |- ( ( A. x -. ph -> -. ph ) -> ( ( A. x ph -> ph ) -> ( A. x ph -> E. x ph ) ) )

  proof
    wph
    wn
    #
    vx
    wal
    #
    @0
    wi
    #
    wph
    wph
    vx
    wex
    #
    wph
    vx
    wal
    @2
    wph
    @1
    wn
    @3
    @1
    wph
    con2
    wph
    vx
    df-ex
    syl6ibr
    imim2d
end
