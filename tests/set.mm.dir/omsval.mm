include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "cdm.mm"
include "cuni.mm"
include "cpw.mm"
include "wss.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "crab.mm"
include "cfv.mm"
include "cesum.mm"
include "cmpt.mm"
include "crn.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "clt.mm"
include "cinf.mm"
include "coms.mm"
include "wceq.mm"
include "df-oms.mm"
include "a1i.mm"
include "dmeq.mm"
include "unieqd.mm"
include "pweqd.mm"
include "rabeq.mm"
include "syl.mm"
include "simpl.mm"
include "fveq1d.mm"
include "esumeq2dv.mm"
include "mpteq12dv.mm"
include "rneqd.mm"
include "infeq1d.mm"
include "adantl.mm"
include "id.mm"
include "dmexg.mm"
include "uniexg.mm"
include "pwexg.mm"
include "mptexg.mm"
include "4syl.mm"
include "fvmptd.mm"

theorem omsval
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let va: setvar a
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w

  disjoint a x
  disjoint a y
  disjoint a z
  disjoint R a
  disjoint x y
  disjoint x z
  disjoint R x
  disjoint y z
  disjoint R y
  disjoint R z
  disjoint a r
  disjoint a s
  disjoint a t
  disjoint a w
  disjoint r s
  disjoint r t
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint R r
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint R s
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint R t
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint R w
  assert |- ( R e. _V -> ( toOMeas ` R ) = ( a e. ~P U. dom R |-> inf ( ran ( x e. { z e. ~P dom R | ( a C_ U. z /\ z ~<_ _om ) } |-> sum* y e. x ( R ` y ) ) , ( 0 [,] +oo ) , < ) ) )

  proof
    cR
    cvv
    wcel
    #
    vr
    cR
    va
    vr
    cv
    #
    cdm
    #
    cuni
    #
    cpw
    #
    vx
    va
    cv
    vz
    cv
    #
    cuni
    wss
    @5
    com
    cdom
    wbr
    wa
    #
    vz
    @2
    cpw
    #
    crab
    #
    vx
    cv
    #
    vy
    cv
    #
    @1
    cfv
    #
    vy
    cesum
    #
    cmpt
    #
    crn
    #
    cc0
    cpnf
    cicc
    co
    #
    clt
    cinf
    #
    cmpt
    #
    va
    cR
    cdm
    #
    cuni
    #
    cpw
    #
    vx
    @6
    vz
    @18
    cpw
    #
    crab
    #
    @9
    @10
    cR
    cfv
    #
    vy
    cesum
    #
    cmpt
    #
    crn
    #
    @15
    clt
    cinf
    #
    cmpt
    #
    cvv
    coms
    cvv
    coms
    vr
    cvv
    @17
    cmpt
    wceq
    @0
    vx
    vy
    vz
    vr
    va
    df-oms
    a1i
    @1
    cR
    wceq
    #
    @17
    @28
    wceq
    @0
    @29
    va
    @4
    @16
    @20
    @27
    @29
    @3
    @19
    @29
    @2
    @18
    @1
    cR
    dmeq
    #
    unieqd
    pweqd
    @29
    @15
    @14
    @26
    clt
    @29
    @13
    @25
    @29
    vx
    @8
    @12
    @22
    @24
    @29
    @7
    @21
    wceq
    @8
    @22
    wceq
    @29
    @2
    @18
    @30
    pweqd
    @6
    vz
    @7
    @21
    rabeq
    syl
    @29
    @9
    @11
    @23
    vy
    @29
    @10
    @9
    wcel
    #
    wa
    @10
    @1
    cR
    @29
    @31
    simpl
    fveq1d
    esumeq2dv
    mpteq12dv
    rneqd
    infeq1d
    mpteq12dv
    adantl
    @0
    id
    @0
    @18
    cvv
    wcel
    @19
    cvv
    wcel
    @20
    cvv
    wcel
    @28
    cvv
    wcel
    cR
    cvv
    dmexg
    @18
    cvv
    uniexg
    @19
    cvv
    pwexg
    va
    @20
    @27
    cvv
    mptexg
    4syl
    fvmptd
end
