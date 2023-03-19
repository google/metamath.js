include "coppc.mm"
include "cfv.mm"
include "ccomf.mm"
include "wceq.mm"
include "cv.mm"
include "cop.mm"
include "cco.mm"
include "co.mm"
include "chom.mm"
include "wral.mm"
include "cbs.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "eqid.mm"
include "chomf.mm"
include "ad2antrr.mm"
include "simplr3.mm"
include "simplr2.mm"
include "simplr1.mm"
include "simprr.mm"
include "oppchom.mm"
include "syl6eleq.mm"
include "simprl.mm"
include "comfeqval.mm"
include "oppcco.mm"
include "homfeqbas.mm"
include "eleqtrd.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "ralrimivvva.mm"
include "oppcbas.mm"
include "a1i.mm"
include "syl6eq.mm"
include "oppchomfpropd.mm"
include "comfeq.mm"
include "mpbird.mm"

theorem oppccomfpropd
  let wph: wff ph
  let cC: class C
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume oppchomfpropd.1: |- ( ph -> ( Homf ` C ) = ( Homf ` D ) )
  assume oppccomfpropd.1: |- ( ph -> ( comf ` C ) = ( comf ` D ) )


  assert |- ( ph -> ( comf ` ( oppCat ` C ) ) = ( comf ` ( oppCat ` D ) ) )

  proof
    wph
    cC
    coppc
    cfv
    #
    ccomf
    cfv
    cD
    coppc
    cfv
    #
    ccomf
    cfv
    wceq
    vg
    cv
    #
    vf
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    vz
    cv
    #
    @0
    cco
    cfv
    #
    co
    co
    #
    @2
    @3
    @6
    @7
    @1
    cco
    cfv
    #
    co
    co
    #
    wceq
    #
    vg
    @5
    @7
    @0
    chom
    cfv
    #
    co
    #
    wral
    vf
    @4
    @5
    @13
    co
    #
    wral
    #
    vz
    cC
    cbs
    cfv
    #
    wral
    vy
    @17
    wral
    vx
    @17
    wral
    wph
    @16
    vx
    vy
    vz
    @17
    @17
    @17
    wph
    @4
    @17
    wcel
    #
    @5
    @17
    wcel
    #
    @7
    @17
    wcel
    #
    w3a
    #
    wa
    #
    @12
    vf
    vg
    @15
    @14
    @22
    @3
    @15
    wcel
    #
    @2
    @14
    wcel
    #
    wa
    #
    wa
    #
    @3
    @2
    @7
    @5
    cop
    #
    @4
    cC
    cco
    cfv
    #
    co
    co
    @3
    @2
    @27
    @4
    cD
    cco
    cfv
    #
    co
    co
    @9
    @11
    @26
    @17
    cC
    cD
    @29
    @28
    @2
    @3
    cC
    chom
    cfv
    #
    @7
    @5
    @4
    @17
    eqid
    #
    @30
    eqid
    #
    @28
    eqid
    #
    @29
    eqid
    #
    wph
    cC
    chomf
    cfv
    cD
    chomf
    cfv
    wceq
    @21
    @25
    oppchomfpropd.1
    ad2antrr
    wph
    cC
    ccomf
    cfv
    cD
    ccomf
    cfv
    wceq
    @21
    @25
    oppccomfpropd.1
    ad2antrr
    @18
    @19
    @20
    wph
    @25
    simplr3
    #
    @18
    @19
    @20
    wph
    @25
    simplr2
    #
    @18
    @19
    @20
    wph
    @25
    simplr1
    #
    @26
    @2
    @14
    @7
    @5
    @30
    co
    @22
    @23
    @24
    simprr
    cC
    @30
    @0
    @5
    @7
    @32
    @0
    eqid
    #
    oppchom
    syl6eleq
    @26
    @3
    @15
    @5
    @4
    @30
    co
    @22
    @23
    @24
    simprl
    cC
    @30
    @0
    @4
    @5
    @32
    @38
    oppchom
    syl6eleq
    comfeqval
    @26
    @17
    cC
    @28
    @3
    @2
    @0
    @4
    @5
    @7
    @31
    @33
    @38
    @37
    @36
    @35
    oppcco
    @26
    cD
    cbs
    cfv
    #
    cD
    @29
    @3
    @2
    @1
    @4
    @5
    @7
    @39
    eqid
    #
    @34
    @1
    eqid
    #
    @26
    @4
    @17
    @39
    @37
    wph
    @17
    @39
    wceq
    @21
    @25
    wph
    cC
    cD
    oppchomfpropd.1
    homfeqbas
    #
    ad2antrr
    #
    eleqtrd
    @26
    @5
    @17
    @39
    @36
    @43
    eleqtrd
    @26
    @7
    @17
    @39
    @35
    @43
    eleqtrd
    oppcco
    3eqtr4d
    ralrimivva
    ralrimivvva
    wph
    vx
    vy
    vz
    @17
    @0
    @1
    @10
    @8
    vf
    vg
    @13
    @8
    eqid
    @10
    eqid
    @13
    eqid
    @17
    @0
    cbs
    cfv
    wceq
    wph
    @17
    cC
    @0
    @38
    @31
    oppcbas
    a1i
    wph
    @17
    @39
    @1
    cbs
    cfv
    @42
    @39
    cD
    @1
    @41
    @40
    oppcbas
    syl6eq
    wph
    cC
    cD
    oppchomfpropd.1
    oppchomfpropd
    comfeq
    mpbird
end
