include "weq.mm"
include "wi.mm"
include "wal.mm"
include "ax-1.mm"
include "alrimiv.mm"
include "wex.mm"
include "exim.mm"
include "ax6ev.mm"
include "pm2.27.mm"
include "ax-mp.mm"
include "ax5e.mm"
include "3syl.mm"
include "impbii.mm"

theorem bj-eqs
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  disjoint ph x
  assert |- ( ph <-> A. x ( x = y -> ph ) )

  proof
    wph
    vx
    vy
    weq
    #
    wph
    wi
    #
    vx
    wal
    #
    wph
    @1
    vx
    wph
    @0
    ax-1
    alrimiv
    @2
    @0
    vx
    wex
    #
    wph
    vx
    wex
    #
    wi
    #
    @4
    wph
    @0
    wph
    vx
    exim
    @3
    @5
    @4
    wi
    vx
    vy
    ax6ev
    @3
    @4
    pm2.27
    ax-mp
    wph
    vx
    ax5e
    3syl
    impbii
end
