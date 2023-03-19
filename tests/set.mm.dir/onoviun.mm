include "wcel.mm"
include "con0.mm"
include "wral.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "ciun.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cuni.mm"
include "cv.mm"
include "wceq.mm"
include "dfiun3g.mm"
include "3ad2ant2.mm"
include "oveq2d.mm"
include "cvv.mm"
include "wss.mm"
include "simp1.mm"
include "mptexg.mm"
include "rnexg.mm"
include "3syl.mm"
include "wf.mm"
include "simp2.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylib.mm"
include "frn.mm"
include "syl.mm"
include "cdm.mm"
include "dmmptg.mm"
include "simp3.mm"
include "eqnetrd.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "onovuni.mm"
include "syl3anc.mm"
include "wrex.mm"
include "wb.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "rexrnmpt.mm"
include "eliun.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "3eqtrd.mm"

theorem onoviun
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cT: class T
  let cF: class F
  let cK: class K
  let cL: class L
  let vw: setvar w
  let cS: class S
  assume onovuni.1: |- ( Lim y -> ( A F y ) = U_ x e. y ( A F x ) )
  assume onovuni.2: |- ( ( x e. On /\ y e. On /\ x C_ y ) -> ( A F x ) C_ ( A F y ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint L x
  disjoint L y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint F w
  disjoint K w
  disjoint L w
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T w
  assert |- ( ( K e. T /\ A. z e. K L e. On /\ K =/= (/) ) -> ( A F U_ z e. K L ) = U_ z e. K ( A F L ) )

  proof
    cK
    cT
    wcel
    #
    cL
    con0
    wcel
    vz
    cK
    wral
    #
    cK
    c0
    wne
    #
    w3a
    #
    cA
    vz
    cK
    cL
    ciun
    #
    cF
    co
    cA
    vz
    cK
    cL
    cmpt
    #
    crn
    #
    cuni
    #
    cF
    co
    #
    vx
    @6
    cA
    vx
    cv
    #
    cF
    co
    #
    ciun
    #
    vz
    cK
    cA
    cL
    cF
    co
    #
    ciun
    #
    @3
    @4
    @7
    cA
    cF
    @1
    @0
    @4
    @7
    wceq
    @2
    vz
    cK
    cL
    con0
    dfiun3g
    3ad2ant2
    oveq2d
    @3
    @6
    cvv
    wcel
    #
    @6
    con0
    wss
    #
    @6
    c0
    wne
    #
    @8
    @11
    wceq
    @3
    @0
    @5
    cvv
    wcel
    @14
    @0
    @1
    @2
    simp1
    vz
    cK
    cL
    cT
    mptexg
    @5
    cvv
    rnexg
    3syl
    @3
    cK
    con0
    @5
    wf
    #
    @15
    @3
    @1
    @17
    @0
    @1
    @2
    simp2
    vz
    cK
    con0
    cL
    @5
    @5
    eqid
    #
    fmpt
    sylib
    cK
    con0
    @5
    frn
    syl
    @3
    @5
    cdm
    #
    c0
    wne
    @16
    @3
    @19
    cK
    c0
    @1
    @0
    @19
    cK
    wceq
    @2
    vz
    cK
    cL
    con0
    dmmptg
    3ad2ant2
    @0
    @1
    @2
    simp3
    eqnetrd
    @19
    c0
    @6
    c0
    @5
    dm0rn0
    necon3bii
    sylib
    vx
    vy
    cA
    @6
    cvv
    cF
    onovuni.1
    onovuni.2
    onovuni
    syl3anc
    @3
    vw
    @11
    @13
    @3
    vw
    cv
    #
    @10
    wcel
    #
    vx
    @6
    wrex
    #
    @20
    @12
    wcel
    #
    vz
    cK
    wrex
    #
    @20
    @11
    wcel
    @20
    @13
    wcel
    @1
    @0
    @22
    @24
    wb
    @2
    @21
    @23
    vz
    vx
    cK
    cL
    @5
    con0
    @18
    @9
    cL
    wceq
    @10
    @12
    @20
    @9
    cL
    cA
    cF
    oveq2
    eleq2d
    rexrnmpt
    3ad2ant2
    vx
    @20
    @6
    @10
    eliun
    vz
    @20
    cK
    @12
    eliun
    3bitr4g
    eqrdv
    3eqtrd
end
