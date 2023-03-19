include "wal.mm"
include "wi.mm"
include "alim.mm"
include "ax-11.mm"
include "syl6.mm"
include "axc4i.mm"

theorem hbalg
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. y ( ph -> A. x ph ) -> A. y ( A. y ph -> A. x A. y ph ) )

  proof
    wph
    wph
    vx
    wal
    #
    wi
    #
    wph
    vy
    wal
    #
    @2
    vx
    wal
    #
    wi
    vy
    @1
    vy
    wal
    @2
    @0
    vy
    wal
    @3
    wph
    @0
    vy
    alim
    wph
    vy
    vx
    ax-11
    syl6
    axc4i
end
