include "wac.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "cin.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "wcel.mm"
include "weu.mm"
include "wex.mm"
include "wal.mm"
include "wel.mm"
include "wn.mm"
include "wo.mm"
include "dfac5.mm"
include "wrex.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "cab.mm"
include "eqid.mm"
include "kmlem13.mm"
include "kmlem8.mm"
include "albii.mm"
include "bitri.mm"
include "df-ne.mm"
include "bicomi.mm"
include "anbi2i.mm"
include "anbi1i.mm"
include "imbi2i.mm"
include "biid.mm"
include "kmlem16.mm"

theorem dfackm
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let vw: setvar w
  let vt: setvar t
  let vh: setvar h

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
  disjoint w x
  disjoint t x
  disjoint h x
  disjoint w y
  disjoint t y
  disjoint h y
  disjoint w z
  disjoint t z
  disjoint h z
  disjoint v w
  disjoint u w
  disjoint t w
  disjoint h w
  disjoint t v
  disjoint h v
  disjoint t u
  disjoint h u
  disjoint h t
  assert |- ( CHOICE <-> A. x E. y A. z E. v A. u ( ( y e. x /\ ( z e. y -> ( ( v e. x /\ -. y = v ) /\ z e. v ) ) ) \/ ( -. y e. x /\ ( z e. x -> ( ( v e. z /\ v e. y ) /\ ( ( u e. z /\ u e. y ) -> u = v ) ) ) ) ) )

  proof
    wac
    vz
    cv
    #
    c0
    wne
    #
    vz
    vx
    cv
    #
    wral
    @0
    vw
    cv
    #
    wne
    #
    @0
    @3
    cin
    #
    c0
    wceq
    wi
    vw
    @2
    wral
    vz
    @2
    wral
    wa
    vv
    cv
    #
    @0
    vy
    cv
    #
    cin
    wcel
    vv
    weu
    #
    vz
    @2
    wral
    #
    vy
    wex
    wi
    vx
    wal
    #
    vy
    vx
    wel
    #
    vz
    vy
    wel
    #
    vv
    vx
    wel
    #
    @7
    @6
    wceq
    wn
    #
    wa
    #
    vz
    vv
    wel
    #
    wa
    #
    wi
    #
    wa
    @11
    wn
    #
    vz
    vx
    wel
    vv
    vz
    wel
    vv
    vy
    wel
    wa
    vu
    vz
    wel
    vu
    vy
    wel
    wa
    vu
    cv
    @6
    wceq
    wi
    wa
    wi
    #
    wa
    wo
    vu
    wal
    vv
    wex
    vz
    wal
    vy
    wex
    #
    vx
    wal
    #
    vx
    vy
    vz
    vw
    vv
    dfac5
    @10
    @4
    @6
    @5
    wcel
    wa
    vw
    @2
    wrex
    #
    vv
    @0
    wral
    vz
    @2
    wrex
    #
    @19
    @9
    wa
    vy
    wex
    wo
    #
    vx
    wal
    #
    @22
    @10
    @24
    wn
    @1
    @8
    wi
    vz
    @2
    wral
    vy
    wex
    wi
    #
    vx
    wal
    @26
    vx
    vy
    vz
    vw
    vv
    vt
    vh
    vt
    cv
    vh
    cv
    #
    @2
    @28
    csn
    cdif
    cuni
    cdif
    wceq
    vh
    @2
    wrex
    vt
    cab
    #
    @29
    eqid
    kmlem13
    @27
    @25
    vx
    @23
    vy
    vz
    vv
    vx
    kmlem8
    albii
    bitri
    @25
    @21
    vx
    @18
    @20
    @9
    vx
    vy
    vz
    vw
    vv
    vu
    @17
    @13
    @7
    @6
    wne
    #
    wa
    #
    @16
    wa
    @12
    @15
    @31
    @16
    @14
    @30
    @13
    @30
    @14
    @7
    @6
    df-ne
    bicomi
    anbi2i
    anbi1i
    imbi2i
    @20
    biid
    @9
    biid
    kmlem16
    albii
    bitri
    bitri
end
