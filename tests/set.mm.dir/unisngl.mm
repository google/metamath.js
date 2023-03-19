include "cuni.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "unieqi.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "simpl.mm"
include "simpr.mm"
include "eleqtrd.mm"
include "exlimiv.mm"
include "eqid.mm"
include "snex.mm"
include "eleq2.mm"
include "eqeq1.mm"
include "anbi12d.mm"
include "spcev.mm"
include "mpan2.mm"
include "impbii.mm"
include "velsn.mm"
include "equcom.mm"
include "3bitri.mm"
include "rexbii.mm"
include "r19.42v.mm"
include "exbii.mm"
include "rexcom4.mm"
include "eluniab.mm"
include "3bitr4ri.mm"
include "risset.mm"
include "3bitr4i.mm"
include "eqriv.mm"
include "eqtr2i.mm"

theorem unisngl
  let vx: setvar x
  let vu: setvar u
  let cC: class C
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  let cV: class V
  let cY: class Y
  assume dissnref.c: |- C = { u | E. x e. X u = { x } }

  disjoint C u
  disjoint C x
  disjoint u x
  disjoint X u
  disjoint X x
  disjoint C y
  disjoint C z
  disjoint u y
  disjoint u z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint V u
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint X y
  disjoint X z
  disjoint Y u
  disjoint Y x
  disjoint Y y
  assert |- X = U. C

  proof
    cC
    cuni
    vu
    cv
    #
    vx
    cv
    #
    csn
    #
    wceq
    #
    vx
    cX
    wrex
    #
    vu
    cab
    #
    cuni
    #
    cX
    cC
    @5
    dissnref.c
    unieqi
    vy
    @6
    cX
    vy
    cv
    #
    @0
    wcel
    #
    @3
    wa
    #
    vu
    wex
    #
    vx
    cX
    wrex
    #
    @1
    @7
    wceq
    #
    vx
    cX
    wrex
    @7
    @6
    wcel
    #
    @7
    cX
    wcel
    @10
    @12
    vx
    cX
    @10
    @7
    @2
    wcel
    #
    @7
    @1
    wceq
    @12
    @10
    @14
    @9
    @14
    vu
    @9
    @7
    @0
    @2
    @8
    @3
    simpl
    @8
    @3
    simpr
    eleqtrd
    exlimiv
    @14
    @2
    @2
    wceq
    #
    @10
    @2
    eqid
    @9
    @14
    @15
    wa
    vu
    @2
    @1
    snex
    @3
    @8
    @14
    @3
    @15
    @0
    @2
    @7
    eleq2
    @0
    @2
    @2
    eqeq1
    anbi12d
    spcev
    mpan2
    impbii
    vy
    @1
    velsn
    vy
    vx
    equcom
    3bitri
    rexbii
    @9
    vx
    cX
    wrex
    #
    vu
    wex
    @8
    @4
    wa
    #
    vu
    wex
    @11
    @13
    @16
    @17
    vu
    @8
    @3
    vx
    cX
    r19.42v
    exbii
    @9
    vx
    vu
    cX
    rexcom4
    @4
    vu
    @7
    eluniab
    3bitr4ri
    vx
    @7
    cX
    risset
    3bitr4i
    eqriv
    eqtr2i
end
