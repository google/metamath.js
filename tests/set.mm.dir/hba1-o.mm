include "wal.mm"
include "wn.mm"
include "ax-c5.mm"
include "con2i.mm"
include "ax10fromc7.mm"
include "con1i.mm"
include "alimi.mm"
include "3syl.mm"

theorem hba1-o
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x ph -> A. x A. x ph )

  proof
    wph
    vx
    wal
    #
    @0
    wn
    #
    vx
    wal
    #
    wn
    #
    @3
    vx
    wal
    @0
    vx
    wal
    @2
    @0
    @1
    vx
    ax-c5
    con2i
    @1
    vx
    ax10fromc7
    @3
    @0
    vx
    @0
    @2
    wph
    vx
    ax10fromc7
    con1i
    alimi
    3syl
end
