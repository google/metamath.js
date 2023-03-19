include "wex.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wmo.mm"
include "eeanv.mm"
include "jcab.mm"
include "2albii.mm"
include "19.26-2.mm"
include "19.23v.mm"
include "albii.mm"
include "alcom.mm"
include "bitri.mm"
include "anbi12i.mm"
include "3bitri.mm"
include "2exbii.mm"
include "mo2v.mm"
include "3bitr4ri.mm"

theorem 2mo2
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
  assert |- ( ( E* x E. y ph /\ E* y E. x ph ) <-> E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) )

  proof
    wph
    vy
    wex
    #
    vx
    vz
    weq
    #
    wi
    #
    vx
    wal
    #
    wph
    vx
    wex
    #
    vy
    vw
    weq
    #
    wi
    #
    vy
    wal
    #
    wa
    #
    vw
    wex
    vz
    wex
    @3
    vz
    wex
    #
    @7
    vw
    wex
    #
    wa
    wph
    @1
    @5
    wa
    wi
    #
    vy
    wal
    vx
    wal
    #
    vw
    wex
    vz
    wex
    @0
    vx
    wmo
    #
    @4
    vy
    wmo
    #
    wa
    @3
    @7
    vz
    vw
    eeanv
    @12
    @8
    vz
    vw
    @12
    wph
    @1
    wi
    #
    wph
    @5
    wi
    #
    wa
    #
    vy
    wal
    vx
    wal
    @15
    vy
    wal
    #
    vx
    wal
    #
    @16
    vy
    wal
    vx
    wal
    #
    wa
    @8
    @11
    @17
    vx
    vy
    wph
    @1
    @5
    jcab
    2albii
    @15
    @16
    vx
    vy
    19.26-2
    @19
    @3
    @20
    @7
    @18
    @2
    vx
    wph
    @1
    vy
    19.23v
    albii
    @20
    @16
    vx
    wal
    #
    vy
    wal
    @7
    @16
    vx
    vy
    alcom
    @21
    @6
    vy
    wph
    @5
    vx
    19.23v
    albii
    bitri
    anbi12i
    3bitri
    2exbii
    @13
    @9
    @14
    @10
    @0
    vx
    vz
    mo2v
    @4
    vy
    vw
    mo2v
    anbi12i
    3bitr4ri
end
