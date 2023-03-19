include "cv.mm"
include "wcel.mm"
include "cuni.mm"
include "cin.mm"
include "csn.mm"
include "cdif.mm"
include "ciun.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "unieqi.mm"
include "vex.mm"
include "difexi.mm"
include "dfiun2.mm"
include "eqtr4i.mm"
include "ineq2i.mm"
include "iunin2.mm"
include "c0.mm"
include "cun.mm"
include "undif2.mm"
include "wss.mm"
include "snssi.mm"
include "ssequn1.mm"
include "sylib.mm"
include "syl5req.mm"
include "iuneq1d.mm"
include "iunxun.mm"
include "difeq1.mm"
include "sneq.mm"
include "difeq2d.mm"
include "unieqd.mm"
include "eqtrd.mm"
include "ineq2d.mm"
include "iunxsn.mm"
include "uneq1i.mm"
include "eqtri.mm"
include "wral.mm"
include "wne.mm"
include "eldifsni.mm"
include "wa.mm"
include "incom.mm"
include "kmlem4.mm"
include "syl5eq.mm"
include "ex.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "iuneq2.mm"
include "syl.mm"
include "iun0.mm"
include "syl6eq.mm"
include "uneq2d.mm"
include "un0.mm"
include "indif.mm"

theorem kmlem11
  let vx: setvar x
  let vz: setvar z
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let vh: setvar h
  let vg: setvar g
  let wph: wff ph
  assume kmlem9.1: |- A = { u | E. t e. x u = ( t \ U. ( x \ { t } ) ) }

  disjoint x z
  disjoint u x
  disjoint t x
  disjoint u z
  disjoint t z
  disjoint t u
  disjoint A z
  disjoint x y
  disjoint w x
  disjoint v x
  disjoint h x
  disjoint g x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint t y
  disjoint h y
  disjoint g y
  disjoint w z
  disjoint v z
  disjoint h z
  disjoint g z
  disjoint v w
  disjoint u w
  disjoint t w
  disjoint h w
  disjoint g w
  disjoint u v
  disjoint t v
  disjoint h v
  disjoint g v
  disjoint h u
  disjoint g u
  disjoint h t
  disjoint g t
  disjoint g h
  disjoint A y
  disjoint A w
  disjoint A v
  disjoint A h
  disjoint A g
  disjoint h ph
  assert |- ( z e. x -> ( z i^i U. A ) = ( z \ U. ( x \ { z } ) ) )

  proof
    vz
    cv
    #
    vx
    cv
    #
    wcel
    #
    @0
    cA
    cuni
    #
    cin
    #
    vt
    @1
    @0
    vt
    cv
    #
    @1
    @5
    csn
    #
    cdif
    #
    cuni
    #
    cdif
    #
    cin
    #
    ciun
    #
    @0
    @1
    @0
    csn
    #
    cdif
    #
    cuni
    #
    cdif
    #
    @4
    @0
    vt
    @1
    @9
    ciun
    #
    cin
    @11
    @3
    @16
    @0
    @3
    vu
    cv
    @9
    wceq
    vt
    @1
    wrex
    vu
    cab
    #
    cuni
    @16
    cA
    @17
    kmlem9.1
    unieqi
    vt
    vu
    @1
    @9
    @5
    @8
    vt
    vex
    difexi
    dfiun2
    eqtr4i
    ineq2i
    vt
    @1
    @0
    @9
    iunin2
    eqtr4i
    @2
    @11
    @0
    @15
    cin
    #
    c0
    cun
    #
    @15
    @2
    @11
    vt
    @12
    @13
    cun
    #
    @10
    ciun
    #
    @19
    @2
    vt
    @1
    @20
    @10
    @2
    @20
    @12
    @1
    cun
    #
    @1
    @12
    @1
    undif2
    @2
    @12
    @1
    wss
    @22
    @1
    wceq
    @0
    @1
    snssi
    @12
    @1
    ssequn1
    sylib
    syl5req
    iuneq1d
    @2
    @21
    @18
    vt
    @13
    @10
    ciun
    #
    cun
    #
    @19
    @21
    vt
    @12
    @10
    ciun
    #
    @23
    cun
    @24
    vt
    @12
    @13
    @10
    iunxun
    @25
    @18
    @23
    vt
    @0
    @10
    @18
    vz
    vex
    @5
    @0
    wceq
    #
    @9
    @15
    @0
    @26
    @9
    @0
    @8
    cdif
    @15
    @5
    @0
    @8
    difeq1
    @26
    @8
    @14
    @0
    @26
    @7
    @13
    @26
    @6
    @12
    @1
    @5
    @0
    sneq
    difeq2d
    unieqd
    difeq2d
    eqtrd
    ineq2d
    iunxsn
    uneq1i
    eqtri
    @2
    @23
    c0
    @18
    @2
    @23
    vt
    @13
    c0
    ciun
    #
    c0
    @2
    @10
    c0
    wceq
    #
    vt
    @13
    wral
    @23
    @27
    wceq
    @2
    @28
    vt
    @13
    @5
    @13
    wcel
    @5
    @0
    wne
    #
    @2
    @28
    @5
    @1
    @0
    eldifsni
    @2
    @29
    @28
    @2
    @29
    wa
    @10
    @9
    @0
    cin
    c0
    @0
    @9
    incom
    vx
    vt
    vz
    kmlem4
    syl5eq
    ex
    syl5
    ralrimiv
    vt
    @13
    @10
    c0
    iuneq2
    syl
    vt
    @13
    iun0
    syl6eq
    uneq2d
    syl5eq
    eqtrd
    @19
    @18
    @15
    @18
    un0
    @0
    @14
    indif
    eqtri
    syl6eq
    syl5eq
end
