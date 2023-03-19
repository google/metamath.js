include "wex.mm"
include "weu.mm"
include "wmo.mm"
include "wal.mm"
include "wi.mm"
include "eumo.mm"
include "2moex.mm"
include "wa.mm"
include "2eu1.mm"
include "simpl.mm"
include "syl6bi.mm"
include "3syl.mm"
include "2exeu.mm"
include "expcom.mm"
include "impbid.mm"

theorem 2eu2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( E! y E. x ph -> ( E! x E! y ph <-> E! x E. y ph ) )

  proof
    wph
    vx
    wex
    #
    vy
    weu
    #
    wph
    vy
    weu
    vx
    weu
    #
    wph
    vy
    wex
    vx
    weu
    #
    @1
    @0
    vy
    wmo
    wph
    vy
    wmo
    vx
    wal
    #
    @2
    @3
    wi
    @0
    vy
    eumo
    wph
    vy
    vx
    2moex
    @4
    @2
    @3
    @1
    wa
    @3
    wph
    vx
    vy
    2eu1
    @3
    @1
    simpl
    syl6bi
    3syl
    @3
    @1
    @2
    wph
    vx
    vy
    2exeu
    expcom
    impbid
end
