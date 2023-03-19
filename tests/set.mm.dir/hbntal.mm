include "wal.mm"
include "wi.mm"
include "wn.mm"
include "hba1.mm"
include "axc7.mm"
include "con1i.mm"
include "con3.mm"
include "al2imi.mm"
include "syl5.mm"
include "alimi.mm"
include "syl.mm"

theorem hbntal
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x ( ph -> A. x ph ) -> A. x ( -. ph -> A. x -. ph ) )

  proof
    wph
    wph
    vx
    wal
    #
    wi
    #
    vx
    wal
    #
    @2
    vx
    wal
    wph
    wn
    #
    @3
    vx
    wal
    #
    wi
    #
    vx
    wal
    @1
    vx
    hba1
    @2
    @5
    vx
    @3
    @0
    wn
    #
    vx
    wal
    #
    @2
    @4
    @7
    wph
    wph
    vx
    axc7
    con1i
    @1
    @6
    @3
    vx
    wph
    @0
    con3
    al2imi
    syl5
    alimi
    syl
end
