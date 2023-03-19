include "cv.mm"
include "wne.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "wn.mm"
include "wex.mm"
include "wo.mm"
include "wal.mm"
include "kmlem14.mm"
include "kmlem15.mm"
include "exbii.mm"
include "orbi12i.mm"
include "19.43.mm"
include "wb.mm"
include "pm3.24.mm"
include "simpl.mm"
include "sps.mm"
include "exlimivv.mm"
include "anim12i.mm"
include "mto.mm"
include "19.33b.mm"
include "ax-mp.mm"
include "exlimiv.mm"
include "bitr2i.mm"
include "albii.mm"
include "bitr3i.mm"
include "3bitr2i.mm"

theorem kmlem16
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  assume kmlem14.1: |- ( ph <-> ( z e. y -> ( ( v e. x /\ y =/= v ) /\ z e. v ) ) )
  assume kmlem14.2: |- ( ps <-> ( z e. x -> ( ( v e. z /\ v e. y ) /\ ( ( u e. z /\ u e. y ) -> u = v ) ) ) )
  assume kmlem14.3: |- ( ch <-> A. z e. x E! v v e. ( z i^i y ) )

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint v w
  disjoint u w
  disjoint u v
  disjoint ph u
  assert |- ( ( E. z e. x A. v e. z E. w e. x ( z =/= w /\ v e. ( z i^i w ) ) \/ E. y ( -. y e. x /\ ch ) ) <-> E. y A. z E. v A. u ( ( y e. x /\ ph ) \/ ( -. y e. x /\ ps ) ) )

  proof
    vz
    cv
    #
    vw
    cv
    #
    wne
    vv
    cv
    @0
    @1
    cin
    wcel
    wa
    vw
    vx
    cv
    #
    wrex
    vv
    @0
    wral
    vz
    @2
    wrex
    #
    vy
    cv
    @2
    wcel
    #
    wn
    #
    wch
    wa
    #
    vy
    wex
    #
    wo
    @4
    wph
    wa
    #
    vu
    wal
    #
    vv
    wex
    #
    vz
    wal
    #
    vy
    wex
    #
    @5
    wps
    wa
    #
    vu
    wal
    #
    vv
    wex
    #
    vz
    wal
    #
    vy
    wex
    #
    wo
    @11
    @16
    wo
    #
    vy
    wex
    @8
    @13
    wo
    vu
    wal
    #
    vv
    wex
    #
    vz
    wal
    #
    vy
    wex
    @3
    @12
    @7
    @17
    wph
    wps
    wch
    vx
    vy
    vz
    vw
    vv
    vu
    kmlem14.1
    kmlem14.2
    kmlem14.3
    kmlem14
    @6
    @16
    vy
    wph
    wps
    wch
    vx
    vy
    vz
    vv
    vu
    kmlem14.1
    kmlem14.2
    kmlem14.3
    kmlem15
    exbii
    orbi12i
    @11
    @16
    vy
    19.43
    @18
    @21
    vy
    @18
    @10
    @15
    wo
    #
    vz
    wal
    #
    @21
    @10
    vz
    wex
    #
    @15
    vz
    wex
    #
    wa
    #
    wn
    @23
    @18
    wb
    @26
    @4
    @5
    wa
    #
    @4
    pm3.24
    #
    @24
    @4
    @25
    @5
    @9
    @4
    vz
    vv
    @8
    @4
    vu
    @4
    wph
    simpl
    #
    sps
    exlimivv
    @14
    @5
    vz
    vv
    @13
    @5
    vu
    @5
    wps
    simpl
    #
    sps
    exlimivv
    anim12i
    mto
    @10
    @15
    vz
    19.33b
    ax-mp
    @22
    @20
    vz
    @20
    @9
    @14
    wo
    #
    vv
    wex
    @22
    @19
    @31
    vv
    @8
    vu
    wex
    #
    @13
    vu
    wex
    #
    wa
    #
    wn
    @19
    @31
    wb
    @34
    @27
    @28
    @32
    @4
    @33
    @5
    @8
    @4
    vu
    @29
    exlimiv
    @13
    @5
    vu
    @30
    exlimiv
    anim12i
    mto
    @8
    @13
    vu
    19.33b
    ax-mp
    exbii
    @9
    @14
    vv
    19.43
    bitr2i
    albii
    bitr3i
    exbii
    3bitr2i
end
