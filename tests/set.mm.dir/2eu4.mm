include "wex.mm"
include "weu.mm"
include "wa.mm"
include "wmo.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "eu5.mm"
include "excom.mm"
include "anbi1i.mm"
include "bitri.mm"
include "anbi12i.mm"
include "anandi.mm"
include "2mo2.mm"
include "anbi2i.mm"
include "3bitr2i.mm"

theorem 2eu4
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
  assert |- ( ( E! x E. y ph /\ E! y E. x ph ) <-> ( E. x E. y ph /\ E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) )

  proof
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
    @0
    vx
    wex
    #
    @0
    vx
    wmo
    #
    wa
    #
    @4
    @2
    vy
    wmo
    #
    wa
    #
    wa
    @4
    @5
    @7
    wa
    #
    wa
    @4
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
    #
    wa
    @1
    @6
    @3
    @8
    @0
    vx
    eu5
    @3
    @2
    vy
    wex
    #
    @7
    wa
    @8
    @2
    vy
    eu5
    @11
    @4
    @7
    wph
    vy
    vx
    excom
    anbi1i
    bitri
    anbi12i
    @4
    @5
    @7
    anandi
    @9
    @10
    @4
    wph
    vx
    vy
    vz
    vw
    2mo2
    anbi2i
    3bitr2i
end
