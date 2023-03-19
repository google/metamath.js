include "wac.mm"
include "cv.mm"
include "wacn.mm"
include "wcel.mm"
include "wal.mm"
include "cvv.mm"
include "vex.mm"
include "wceq.mm"
include "acacni.mm"
include "mpan2.mm"
include "syl5eleqr.mm"
include "alrimiv.mm"
include "cpw.mm"
include "vpwex.mm"
include "id.mm"
include "acneq.mm"
include "eleq12d.mm"
include "spcv.mm"
include "ccrd.mm"
include "cdm.mm"
include "csdm.mm"
include "wbr.mm"
include "cdom.mm"
include "wi.mm"
include "canth2.mm"
include "sdomdom.mm"
include "acndom2.mm"
include "mp2b.mm"
include "acnnum.mm"
include "sylib.mm"
include "numacn.mm"
include "mpsyl.mm"
include "syl.mm"
include "a1i.mm"
include "2thd.mm"
include "eqrdv.mm"
include "dfacacn.mm"
include "sylibr.mm"
include "impbii.mm"

theorem dfac13
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cV: class V


  assert |- ( CHOICE <-> A. x x e. AC_ x )

  proof
    wac
    vx
    cv
    #
    @0
    wacn
    #
    wcel
    #
    vx
    wal
    #
    wac
    @2
    vx
    wac
    @0
    cvv
    @1
    vx
    vex
    #
    wac
    @0
    cvv
    wcel
    @1
    cvv
    wceq
    @4
    @0
    cvv
    acacni
    mpan2
    syl5eleqr
    alrimiv
    @3
    vy
    cv
    #
    wacn
    #
    cvv
    wceq
    #
    vy
    wal
    wac
    @3
    @7
    vy
    @3
    vz
    @6
    cvv
    @3
    vz
    cv
    #
    @6
    wcel
    #
    @8
    cvv
    wcel
    #
    @3
    @8
    cpw
    #
    @11
    wacn
    #
    wcel
    #
    @9
    @2
    @13
    vx
    @11
    vz
    vpwex
    @0
    @11
    wceq
    #
    @0
    @11
    @1
    @12
    @14
    id
    @0
    @11
    acneq
    eleq12d
    spcv
    @5
    cvv
    wcel
    @13
    @8
    ccrd
    cdm
    wcel
    #
    @9
    vy
    vex
    @13
    @8
    @12
    wcel
    #
    @15
    @8
    @11
    csdm
    wbr
    @8
    @11
    cdom
    wbr
    @13
    @16
    wi
    @8
    vz
    vex
    #
    canth2
    @8
    @11
    sdomdom
    @11
    @8
    @11
    acndom2
    mp2b
    @8
    acnnum
    sylib
    @5
    cvv
    @8
    numacn
    mpsyl
    syl
    @10
    @3
    @17
    a1i
    2thd
    eqrdv
    alrimiv
    vy
    dfacacn
    sylibr
    impbii
end
