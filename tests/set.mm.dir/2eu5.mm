include "weu.mm"
include "wmo.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "weq.mm"
include "wi.mm"
include "2eu1.mm"
include "pm5.32ri.mm"
include "eumo.mm"
include "adantl.mm"
include "2moex.mm"
include "syl.mm"
include "pm4.71i.mm"
include "2eu4.mm"
include "3bitr2i.mm"

theorem 2eu5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint ph z
  disjoint ph w
  assert |- ( ( E! x E! y ph /\ A. x E* y ph ) <-> ( E. x E. y ph /\ E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) )

  proof
    wph
    vy
    weu
    vx
    weu
    #
    wph
    vy
    wmo
    vx
    wal
    #
    wa
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
    #
    vy
    weu
    #
    wa
    #
    @1
    wa
    @6
    @2
    vx
    wex
    wph
    vx
    vz
    weq
    vy
    vw
    weq
    wa
    wi
    vy
    wal
    vx
    wal
    vw
    wex
    vz
    wex
    wa
    @1
    @0
    @6
    wph
    vx
    vy
    2eu1
    pm5.32ri
    @6
    @1
    @6
    @4
    vy
    wmo
    #
    @1
    @5
    @7
    @3
    @4
    vy
    eumo
    adantl
    wph
    vy
    vx
    2moex
    syl
    pm4.71i
    wph
    vx
    vy
    vz
    vw
    2eu4
    3bitr2i
end
