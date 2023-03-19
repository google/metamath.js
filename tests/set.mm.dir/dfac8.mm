include "wac.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "wal.mm"
include "wwe.mm"
include "dfac3.mm"
include "ccrd.mm"
include "cdm.mm"
include "cvv.mm"
include "cpw.mm"
include "vex.mm"
include "vpwex.mm"
include "wceq.mm"
include "raleq.mm"
include "exbidv.mm"
include "spcv.mm"
include "dfac8a.mm"
include "mpsyl.mm"
include "dfac8b.mm"
include "syl.mm"
include "alrimiv.mm"
include "cuni.mm"
include "vuniex.mm"
include "weeq2.mm"
include "dfac8c.mm"
include "impbii.mm"
include "bitri.mm"

theorem dfac8
  let vx: setvar x
  let vr: setvar r
  let vf: setvar f
  let vy: setvar y
  let vz: setvar z

  disjoint r x
  disjoint f r
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint r y
  disjoint r z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( CHOICE <-> A. x E. r r We x )

  proof
    wac
    vz
    cv
    #
    c0
    wne
    @0
    vf
    cv
    cfv
    @0
    wcel
    wi
    #
    vz
    vy
    cv
    #
    wral
    #
    vf
    wex
    #
    vy
    wal
    #
    vx
    cv
    #
    vr
    cv
    #
    wwe
    #
    vr
    wex
    #
    vx
    wal
    #
    vy
    vz
    vf
    dfac3
    @5
    @10
    @5
    @9
    vx
    @5
    @6
    ccrd
    cdm
    wcel
    #
    @9
    @6
    cvv
    wcel
    @5
    @1
    vz
    @6
    cpw
    #
    wral
    #
    vf
    wex
    #
    @11
    vx
    vex
    @4
    @14
    vy
    @12
    vx
    vpwex
    @2
    @12
    wceq
    @3
    @13
    vf
    @1
    vz
    @2
    @12
    raleq
    exbidv
    spcv
    vz
    @6
    cvv
    vf
    dfac8a
    mpsyl
    vr
    @6
    dfac8b
    syl
    alrimiv
    @10
    @4
    vy
    @2
    cvv
    wcel
    @10
    @2
    cuni
    #
    @7
    wwe
    #
    vr
    wex
    #
    @4
    vy
    vex
    @9
    @17
    vx
    @15
    vy
    vuniex
    @6
    @15
    wceq
    @8
    @16
    vr
    @6
    @15
    @7
    weeq2
    exbidv
    spcv
    vz
    @2
    cvv
    vf
    vr
    dfac8c
    mpsyl
    alrimiv
    impbii
    bitri
end
