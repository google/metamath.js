include "cv.mm"
include "wne.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wi.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "wrex.mm"
include "vex.mm"
include "weq.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab2.mm"
include "difeq1.mm"
include "sneq.mm"
include "difeq2d.mm"
include "unieqd.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "bitri.mm"
include "wa.mm"
include "reeanv.mm"
include "eqeq12.mm"
include "syl5ibr.mm"
include "necon3d.mm"
include "kmlem5.mm"
include "ineq12.mm"
include "eqeq1d.mm"
include "expd.mm"
include "syl5d.mm"
include "com12.mm"
include "adantl.mm"
include "rexlimivv.mm"
include "sylbir.mm"
include "syl2anb.mm"
include "rgen2a.mm"

theorem kmlem9
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let vy: setvar y
  let vv: setvar v
  let vh: setvar h
  let vg: setvar g
  let wph: wff ph
  assume kmlem9.1: |- A = { u | E. t e. x u = ( t \ U. ( x \ { t } ) ) }

  disjoint x z
  disjoint w x
  disjoint u x
  disjoint t x
  disjoint w z
  disjoint u z
  disjoint t z
  disjoint u w
  disjoint t w
  disjoint t u
  disjoint A z
  disjoint A w
  disjoint x y
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
  disjoint v z
  disjoint h z
  disjoint g z
  disjoint v w
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
  disjoint A v
  disjoint A h
  disjoint A g
  disjoint h ph
  assert |- A. z e. A A. w e. A ( z =/= w -> ( z i^i w ) = (/) )

  proof
    vz
    cv
    #
    vw
    cv
    #
    wne
    #
    @0
    @1
    cin
    #
    c0
    wceq
    #
    wi
    #
    vz
    vw
    cA
    @0
    cA
    wcel
    @0
    vt
    cv
    #
    vx
    cv
    #
    @6
    csn
    #
    cdif
    #
    cuni
    #
    cdif
    #
    wceq
    #
    vt
    @7
    wrex
    #
    @1
    vh
    cv
    #
    @7
    @14
    csn
    #
    cdif
    #
    cuni
    #
    cdif
    #
    wceq
    #
    vh
    @7
    wrex
    #
    @5
    @1
    cA
    wcel
    #
    vu
    cv
    #
    @11
    wceq
    #
    vt
    @7
    wrex
    #
    @13
    vu
    @0
    cA
    vz
    vex
    vu
    vz
    weq
    @23
    @12
    vt
    @7
    @22
    @0
    @11
    eqeq1
    rexbidv
    kmlem9.1
    elab2
    @21
    @1
    @11
    wceq
    #
    vt
    @7
    wrex
    #
    @20
    @24
    @26
    vu
    @1
    cA
    vw
    vex
    vu
    vw
    weq
    @23
    @25
    vt
    @7
    @22
    @1
    @11
    eqeq1
    rexbidv
    kmlem9.1
    elab2
    @25
    @19
    vt
    vh
    @7
    vt
    vh
    weq
    #
    @11
    @18
    @1
    @27
    @11
    @14
    @10
    cdif
    @18
    @6
    @14
    @10
    difeq1
    @27
    @10
    @17
    @14
    @27
    @9
    @16
    @27
    @8
    @15
    @7
    @6
    @14
    sneq
    difeq2d
    unieqd
    difeq2d
    eqtrd
    #
    eqeq2d
    cbvrexv
    bitri
    @13
    @20
    wa
    @12
    @19
    wa
    #
    vh
    @7
    wrex
    vt
    @7
    wrex
    @5
    @12
    @19
    vt
    vh
    @7
    @7
    reeanv
    @29
    @5
    vt
    vh
    @7
    @7
    @14
    @7
    wcel
    #
    @29
    @5
    wi
    @6
    @7
    wcel
    @29
    @30
    @5
    @29
    @2
    @6
    @14
    wne
    #
    @30
    @4
    @29
    @6
    @14
    @0
    @1
    @27
    vz
    vw
    weq
    @29
    @11
    @18
    wceq
    @28
    @0
    @11
    @1
    @18
    eqeq12
    syl5ibr
    necon3d
    @29
    @30
    @31
    @4
    @30
    @31
    wa
    @4
    @29
    @11
    @18
    cin
    #
    c0
    wceq
    vx
    vt
    vh
    kmlem5
    @29
    @3
    @32
    c0
    @0
    @11
    @1
    @18
    ineq12
    eqeq1d
    syl5ibr
    expd
    syl5d
    com12
    adantl
    rexlimivv
    sylbir
    syl2anb
    rgen2a
end
