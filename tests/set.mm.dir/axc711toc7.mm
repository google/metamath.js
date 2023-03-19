include "wal.mm"
include "wn.mm"
include "hba1-o.mm"
include "con3i.mm"
include "alimi.mm"
include "axc711.mm"
include "ax-c5.mm"
include "3syl.mm"

theorem axc711toc7
  let wph: wff ph
  let vx: setvar x


  assert |- ( -. A. x -. A. x ph -> ph )

  proof
    wph
    vx
    wal
    #
    wn
    #
    vx
    wal
    #
    wn
    @0
    vx
    wal
    #
    wn
    #
    vx
    wal
    #
    wn
    @0
    wph
    @5
    @2
    @4
    @1
    vx
    @0
    @3
    wph
    vx
    hba1-o
    con3i
    alimi
    con3i
    wph
    vx
    vx
    axc711
    wph
    vx
    ax-c5
    3syl
end
