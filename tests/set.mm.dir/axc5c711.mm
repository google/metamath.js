include "wal.mm"
include "wn.mm"
include "ax-c5.mm"
include "ax10fromc7.mm"
include "ax-c7.mm"
include "con1i.mm"
include "alimi.mm"
include "ax-11.mm"
include "3syl.mm"
include "nsyl4.mm"
include "ja.mm"

theorem axc5c711
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A. x A. y -. A. x A. y ph -> A. x ph ) -> ph )

  proof
    wph
    vy
    wal
    #
    vx
    wal
    wn
    #
    vy
    wal
    vx
    wal
    #
    wph
    vx
    wal
    wph
    @0
    wph
    @2
    wph
    vy
    ax-c5
    @0
    wn
    #
    @3
    vy
    wal
    @1
    vx
    wal
    #
    vy
    wal
    @2
    wph
    vy
    ax10fromc7
    @3
    @4
    vy
    @4
    @0
    @0
    vx
    ax-c7
    con1i
    alimi
    @1
    vy
    vx
    ax-11
    3syl
    nsyl4
    wph
    vx
    ax-c5
    ja
end
