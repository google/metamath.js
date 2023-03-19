include "wal.mm"
include "wi.mm"
include "hba1.mm"
include "idn1.mm"
include "alim.mm"
include "e1a.mm"
include "ax-11.mm"
include "imim1.mm"
include "e10.mm"
include "gen11nv.mm"
include "in1.mm"

theorem hbalgVD
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
    vy
    wal
    #
    wph
    vy
    wal
    #
    @3
    vx
    wal
    #
    wi
    #
    vy
    wal
    @2
    @5
    vy
    @1
    vy
    hba1
    @2
    @3
    @0
    vy
    wal
    #
    wi
    #
    @6
    @4
    wi
    @5
    @2
    @2
    @7
    @2
    idn1
    wph
    @0
    vy
    alim
    e1a
    wph
    vy
    vx
    ax-11
    @3
    @6
    @4
    imim1
    e10
    gen11nv
    in1
end
