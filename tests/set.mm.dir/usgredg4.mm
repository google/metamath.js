include "cusgr.mm"
include "wcel.mm"
include "cdm.mm"
include "cfv.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "wne.mm"
include "wi.mm"
include "usgredg3.mm"
include "wb.mm"
include "eleq2.mm"
include "adantl.mm"
include "wo.mm"
include "simplrr.mm"
include "weq.mm"
include "preq2.mm"
include "eqeq2d.mm"
include "eqidd.mm"
include "rspcedvd.mm"
include "simprr.mm"
include "preq1.mm"
include "eqeqan12rd.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "ex.mm"
include "simplrl.mm"
include "prcom.mm"
include "a1i.mm"
include "jaoi.mm"
include "elpri.mm"
include "syl11.mm"
include "sylbid.mm"
include "rexlimdvva.mm"
include "mpd.mm"
include "3impia.mm"

theorem usgredg4
  let vy: setvar y
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vz: setvar z
  assume usgredg3.v: |- V = ( Vtx ` G )
  assume usgredg3.e: |- E = ( iEdg ` G )

  disjoint E y
  disjoint G y
  disjoint V y
  disjoint X y
  disjoint Y y
  disjoint E x
  disjoint x y
  disjoint G x
  disjoint V x
  disjoint X x
  disjoint E z
  disjoint x z
  disjoint G z
  disjoint V z
  disjoint X z
  disjoint Y x
  disjoint Y z
  disjoint y z
  assert |- ( ( G e. USGraph /\ X e. dom E /\ Y e. ( E ` X ) ) -> E. y e. V ( E ` X ) = { Y , y } )

  proof
    cG
    cusgr
    wcel
    #
    cX
    cE
    cdm
    wcel
    #
    cY
    cX
    cE
    cfv
    #
    wcel
    #
    @2
    cY
    vy
    cv
    #
    cpr
    #
    wceq
    #
    vy
    cV
    wrex
    #
    @0
    @1
    wa
    #
    vx
    cv
    #
    vz
    cv
    #
    wne
    #
    @2
    @9
    @10
    cpr
    #
    wceq
    #
    wa
    #
    vz
    cV
    wrex
    vx
    cV
    wrex
    @3
    @7
    wi
    #
    vx
    vz
    cE
    cG
    cV
    cX
    usgredg3.v
    usgredg3.e
    usgredg3
    @8
    @14
    @15
    vx
    vz
    cV
    cV
    @8
    @9
    cV
    wcel
    #
    @10
    cV
    wcel
    #
    wa
    wa
    #
    @14
    @15
    @18
    @14
    wa
    #
    @3
    cY
    @12
    wcel
    #
    @7
    @14
    @3
    @20
    wb
    #
    @18
    @13
    @21
    @11
    @2
    @12
    cY
    eleq2
    adantl
    adantl
    cY
    @9
    wceq
    #
    cY
    @10
    wceq
    #
    wo
    @19
    @7
    @20
    @22
    @19
    @7
    wi
    @23
    @22
    @19
    @7
    @22
    @19
    wa
    #
    @7
    @12
    @9
    @4
    cpr
    #
    wceq
    #
    vy
    cV
    wrex
    @24
    @26
    @12
    @12
    wceq
    #
    vy
    @10
    cV
    @19
    @17
    @22
    @8
    @16
    @17
    @14
    simplrr
    adantl
    vy
    vz
    weq
    #
    @26
    @27
    wb
    @24
    @28
    @25
    @12
    @12
    @4
    @10
    @9
    preq2
    eqeq2d
    adantl
    @24
    @12
    eqidd
    rspcedvd
    @24
    @6
    @26
    vy
    cV
    @19
    @22
    @2
    @12
    @5
    @25
    @18
    @11
    @13
    simprr
    #
    cY
    @9
    @4
    preq1
    eqeqan12rd
    rexbidv
    mpbird
    ex
    @23
    @19
    @7
    @23
    @19
    wa
    #
    @7
    @12
    @10
    @4
    cpr
    #
    wceq
    #
    vy
    cV
    wrex
    @30
    @32
    @12
    @10
    @9
    cpr
    #
    wceq
    #
    vy
    @9
    cV
    @19
    @16
    @23
    @8
    @16
    @17
    @14
    simplrl
    adantl
    vy
    vx
    weq
    #
    @32
    @34
    wb
    @30
    @35
    @31
    @33
    @12
    @4
    @9
    @10
    preq2
    eqeq2d
    adantl
    @34
    @30
    @9
    @10
    prcom
    a1i
    rspcedvd
    @30
    @6
    @32
    vy
    cV
    @19
    @23
    @2
    @12
    @5
    @31
    @29
    cY
    @10
    @4
    preq1
    eqeqan12rd
    rexbidv
    mpbird
    ex
    jaoi
    cY
    @9
    @10
    elpri
    syl11
    sylbid
    ex
    rexlimdvva
    mpd
    3impia
end
