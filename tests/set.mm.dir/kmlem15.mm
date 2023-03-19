include "wel.mm"
include "wn.mm"
include "wa.mm"
include "wal.mm"
include "wex.mm"
include "cv.mm"
include "cin.mm"
include "wcel.mm"
include "weu.mm"
include "wral.mm"
include "weq.mm"
include "wi.mm"
include "wsb.mm"
include "nfv.mm"
include "eu1.mm"
include "elin.mm"
include "clelsb3.mm"
include "bitri.mm"
include "equcom.mm"
include "imbi12i.mm"
include "albii.mm"
include "anbi12i.mm"
include "19.28v.mm"
include "bitr4i.mm"
include "exbii.mm"
include "ralbii.mm"
include "df-ral.mm"
include "19.21v.mm"
include "19.37v.mm"
include "3bitri.mm"
include "anbi2i.mm"
include "19.42v.mm"
include "bitr2i.mm"
include "3bitr2i.mm"

theorem kmlem15
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let vw: setvar w
  assume kmlem14.1: |- ( ph <-> ( z e. y -> ( ( v e. x /\ y =/= v ) /\ z e. v ) ) )
  assume kmlem14.2: |- ( ps <-> ( z e. x -> ( ( v e. z /\ v e. y ) /\ ( ( u e. z /\ u e. y ) -> u = v ) ) ) )
  assume kmlem14.3: |- ( ch <-> A. z e. x E! v v e. ( z i^i y ) )

  disjoint x y
  disjoint x z
  disjoint v x
  disjoint u x
  disjoint y z
  disjoint v y
  disjoint u y
  disjoint v z
  disjoint u z
  disjoint u v
  disjoint ph u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint v w
  disjoint u w
  assert |- ( ( -. y e. x /\ ch ) <-> A. z E. v A. u ( -. y e. x /\ ps ) )

  proof
    vy
    vx
    wel
    wn
    #
    wch
    wa
    @0
    wps
    vu
    wal
    #
    vv
    wex
    #
    vz
    wal
    #
    wa
    @0
    @2
    wa
    #
    vz
    wal
    @0
    wps
    wa
    vu
    wal
    #
    vv
    wex
    #
    vz
    wal
    wch
    @3
    @0
    wch
    vv
    cv
    #
    vz
    cv
    #
    vy
    cv
    #
    cin
    #
    wcel
    #
    vv
    weu
    #
    vz
    vx
    cv
    #
    wral
    vv
    vz
    wel
    vv
    vy
    wel
    wa
    #
    vu
    vz
    wel
    vu
    vy
    wel
    wa
    #
    vu
    vv
    weq
    #
    wi
    #
    wa
    #
    vu
    wal
    #
    vv
    wex
    #
    vz
    @13
    wral
    #
    @3
    kmlem14.3
    @12
    @20
    vz
    @13
    @12
    @11
    @11
    vv
    vu
    wsb
    #
    vv
    vu
    weq
    #
    wi
    #
    vu
    wal
    #
    wa
    #
    vv
    wex
    @20
    @11
    vv
    vu
    @11
    vu
    nfv
    eu1
    @26
    @19
    vv
    @26
    @14
    @17
    vu
    wal
    #
    wa
    @19
    @11
    @14
    @25
    @27
    @7
    @8
    @9
    elin
    @24
    @17
    vu
    @22
    @15
    @23
    @16
    @22
    vu
    cv
    #
    @10
    wcel
    @15
    vu
    vv
    @10
    clelsb3
    @28
    @8
    @9
    elin
    bitri
    vv
    vu
    equcom
    imbi12i
    albii
    anbi12i
    @14
    @17
    vu
    19.28v
    bitr4i
    exbii
    bitri
    ralbii
    @21
    vz
    vx
    wel
    #
    @20
    wi
    #
    vz
    wal
    @3
    @20
    vz
    @13
    df-ral
    @2
    @30
    vz
    @2
    @29
    @19
    wi
    #
    vv
    wex
    @30
    @1
    @31
    vv
    @1
    @29
    @18
    wi
    #
    vu
    wal
    @31
    wps
    @32
    vu
    kmlem14.2
    albii
    @29
    @18
    vu
    19.21v
    bitri
    exbii
    @29
    @19
    vv
    19.37v
    bitri
    albii
    bitr4i
    3bitri
    anbi2i
    @0
    @2
    vz
    19.28v
    @4
    @6
    vz
    @6
    @0
    @1
    wa
    #
    vv
    wex
    @4
    @5
    @33
    vv
    @0
    wps
    vu
    19.28v
    exbii
    @0
    @1
    vv
    19.42v
    bitr2i
    albii
    3bitr2i
end
