include "wal.mm"
include "wi.mm"
include "alim.mm"
include "ax-11.mm"
include "syl6.mm"

theorem bj-hbalt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. y ( ph -> A. x ph ) -> ( A. y ph -> A. x A. y ph ) )

  proof
    wph
    wph
    vx
    wal
    #
    wi
    vy
    wal
    wph
    vy
    wal
    #
    @0
    vy
    wal
    @1
    vx
    wal
    wph
    @0
    vy
    alim
    wph
    vy
    vx
    ax-11
    syl6
end
