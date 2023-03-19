include "con0.mm"
include "wcel.mm"
include "ccf.mm"
include "cfv.mm"
include "cv.mm"
include "ccrd.mm"
include "wceq.mm"
include "wss.mm"
include "cuni.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cint.mm"
include "wrex.mm"
include "wral.mm"
include "cfval.mm"
include "dfss3.mm"
include "wi.mm"
include "ssel.mm"
include "onelon.mm"
include "ex.mm"
include "sylan9r.mm"
include "onelss.mm"
include "syl6.mm"
include "imdistand.mm"
include "ancomsd.mm"
include "eximdv.mm"
include "eluni.mm"
include "df-rex.mm"
include "3imtr4g.mm"
include "ralimdv.mm"
include "syl5bi.mm"
include "imdistanda.mm"
include "anim2d.mm"
include "ss2abdv.mm"
include "intss.mm"
include "syl.mm"
include "eqsstrd.mm"
include "wn.mm"
include "c0.mm"
include "cdm.mm"
include "cff.mm"
include "fdmi.mm"
include "eleq2i.mm"
include "ndmfv.mm"
include "sylnbir.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "pm2.61i.mm"

theorem cfub
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint w z
  disjoint v z
  disjoint A z
  disjoint v w
  disjoint A w
  disjoint A v
  assert |- ( cf ` A ) C_ |^| { x | E. y ( x = ( card ` y ) /\ ( y C_ A /\ A C_ U. y ) ) }

  proof
    cA
    con0
    wcel
    #
    cA
    ccf
    cfv
    #
    vx
    cv
    vy
    cv
    #
    ccrd
    cfv
    wceq
    #
    @2
    cA
    wss
    #
    cA
    @2
    cuni
    #
    wss
    #
    wa
    #
    wa
    #
    vy
    wex
    #
    vx
    cab
    #
    cint
    #
    wss
    @0
    @1
    @3
    @4
    vz
    cv
    #
    vw
    cv
    #
    wss
    #
    vw
    @2
    wrex
    #
    vz
    cA
    wral
    #
    wa
    #
    wa
    #
    vy
    wex
    #
    vx
    cab
    #
    cint
    #
    @11
    vx
    vy
    vz
    vw
    cA
    cfval
    @0
    @10
    @20
    wss
    @21
    @11
    wss
    @0
    @9
    @19
    vx
    @0
    @8
    @18
    vy
    @0
    @7
    @17
    @3
    @0
    @4
    @6
    @16
    @6
    @12
    @5
    wcel
    #
    vz
    cA
    wral
    @0
    @4
    wa
    #
    @16
    vz
    cA
    @5
    dfss3
    @23
    @22
    @15
    vz
    cA
    @23
    @12
    @13
    wcel
    #
    @13
    @2
    wcel
    #
    wa
    #
    vw
    wex
    @25
    @14
    wa
    #
    vw
    wex
    @22
    @15
    @23
    @26
    @27
    vw
    @23
    @25
    @24
    @27
    @23
    @25
    @24
    @14
    @23
    @25
    @13
    con0
    wcel
    #
    @24
    @14
    wi
    @4
    @25
    @13
    cA
    wcel
    #
    @0
    @28
    @2
    cA
    @13
    ssel
    @0
    @29
    @28
    cA
    @13
    onelon
    ex
    sylan9r
    @13
    @12
    onelss
    syl6
    imdistand
    ancomsd
    eximdv
    vw
    @12
    @2
    eluni
    @14
    vw
    @2
    df-rex
    3imtr4g
    ralimdv
    syl5bi
    imdistanda
    anim2d
    eximdv
    ss2abdv
    @10
    @20
    intss
    syl
    eqsstrd
    @0
    wn
    @1
    c0
    @11
    @0
    cA
    ccf
    cdm
    #
    wcel
    @1
    c0
    wceq
    @30
    con0
    cA
    con0
    con0
    ccf
    cff
    fdmi
    eleq2i
    cA
    ccf
    ndmfv
    sylnbir
    @11
    0ss
    syl6eqss
    pm2.61i
end
