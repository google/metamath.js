include "wmo.mm"
include "wal.mm"
include "weu.mm"
include "wex.mm"
include "wa.mm"
include "wi.mm"
include "2eu2ex.mm"
include "df-mo.mm"
include "albii.mm"
include "euim.mm"
include "ex.mm"
include "syl5bi.mm"
include "syl.mm"
include "pm2.43b.mm"
include "2euswap.mm"
include "syld.mm"
include "jcad.mm"
include "2exeu.mm"
include "impbid1.mm"

theorem 2eu1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x E* y ph -> ( E! x E! y ph <-> ( E! x E. y ph /\ E! y E. x ph ) ) )

  proof
    wph
    vy
    wmo
    #
    vx
    wal
    #
    wph
    vy
    weu
    #
    vx
    weu
    #
    wph
    vy
    wex
    #
    vx
    weu
    #
    wph
    vx
    wex
    vy
    weu
    #
    wa
    @1
    @3
    @5
    @6
    @1
    @3
    @5
    @3
    @4
    vx
    wex
    #
    @1
    @3
    @5
    wi
    #
    wi
    wph
    vx
    vy
    2eu2ex
    @1
    @4
    @2
    wi
    #
    vx
    wal
    #
    @7
    @8
    @0
    @9
    vx
    wph
    vy
    df-mo
    albii
    @7
    @10
    @8
    @4
    @2
    vx
    euim
    ex
    syl5bi
    syl
    pm2.43b
    #
    @1
    @3
    @5
    @6
    @11
    wph
    vx
    vy
    2euswap
    syld
    jcad
    wph
    vx
    vy
    2exeu
    impbid1
end
