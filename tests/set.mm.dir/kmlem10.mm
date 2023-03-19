include "cv.mm"
include "wne.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "wal.mm"
include "kmlem9.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "wrex.mm"
include "cab.mm"
include "cvv.mm"
include "vex.mm"
include "abrexex.mm"
include "eqeltri.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "spcv.mm"
include "mpi.mm"

theorem kmlem10
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let vh: setvar h
  let vv: setvar v
  let vg: setvar g
  assume kmlem9.1: |- A = { u | E. t e. x u = ( t \ U. ( x \ { t } ) ) }

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint u x
  disjoint t x
  disjoint h x
  disjoint y z
  disjoint w y
  disjoint u y
  disjoint t y
  disjoint h y
  disjoint w z
  disjoint u z
  disjoint t z
  disjoint h z
  disjoint u w
  disjoint t w
  disjoint h w
  disjoint t u
  disjoint h u
  disjoint h t
  disjoint A y
  disjoint A z
  disjoint A w
  disjoint A h
  disjoint h ph
  disjoint v x
  disjoint g x
  disjoint v y
  disjoint g y
  disjoint v z
  disjoint g z
  disjoint v w
  disjoint g w
  disjoint u v
  disjoint t v
  disjoint h v
  disjoint g v
  disjoint g u
  disjoint g t
  disjoint g h
  disjoint A v
  disjoint A g
  assert |- ( A. h ( A. z e. h A. w e. h ( z =/= w -> ( z i^i w ) = (/) ) -> E. y A. z e. h ph ) -> E. y A. z e. A ph )

  proof
    vz
    cv
    #
    vw
    cv
    #
    wne
    @0
    @1
    cin
    c0
    wceq
    wi
    #
    vw
    vh
    cv
    #
    wral
    #
    vz
    @3
    wral
    #
    wph
    vz
    @3
    wral
    #
    vy
    wex
    #
    wi
    #
    vh
    wal
    @2
    vw
    cA
    wral
    #
    vz
    cA
    wral
    #
    wph
    vz
    cA
    wral
    #
    vy
    wex
    #
    vx
    vz
    vw
    vu
    vt
    cA
    kmlem9.1
    kmlem9
    @8
    @10
    @12
    wi
    vh
    cA
    cA
    vu
    cv
    vt
    cv
    #
    vx
    cv
    #
    @13
    csn
    cdif
    cuni
    cdif
    #
    wceq
    vt
    @14
    wrex
    vu
    cab
    cvv
    kmlem9.1
    vt
    vu
    @14
    @15
    vx
    vex
    abrexex
    eqeltri
    @3
    cA
    wceq
    #
    @5
    @10
    @7
    @12
    @4
    @9
    vz
    @3
    cA
    @2
    vw
    @3
    cA
    raleq
    raleqbi1dv
    @16
    @6
    @11
    vy
    wph
    vz
    @3
    cA
    raleq
    exbidv
    imbi12d
    spcv
    mpi
end
