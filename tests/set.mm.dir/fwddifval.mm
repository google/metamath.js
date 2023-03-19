include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "cmin.mm"
include "wcel.mm"
include "crab.mm"
include "cfwddif.mm"
include "cvv.mm"
include "cdm.mm"
include "cmpt.mm"
include "cc.mm"
include "cpm.mm"
include "wceq.mm"
include "df-fwddif.mm"
include "a1i.mm"
include "dmeq.mm"
include "eleq2d.mm"
include "rabeqbidv.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "mpteq12dv.mm"
include "adantl.mm"
include "wf.mm"
include "wss.mm"
include "wa.mm"
include "cnex.mm"
include "elpm2r.mm"
include "mpanl12.mm"
include "syl2anc.mm"
include "fdm.mm"
include "syl.mm"
include "ssexd.mm"
include "eqeltrd.mm"
include "rabexg.mm"
include "mptexg.mm"
include "3syl.mm"
include "fvmptd.mm"
include "mpteq1d.mm"
include "eqtrd.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ovexd.mm"

theorem fwddifval
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  assume fwddifval.1: |- ( ph -> A C_ CC )
  assume fwddifval.2: |- ( ph -> F : A --> CC )
  assume fwddifval.3: |- ( ph -> X e. A )
  assume fwddifval.4: |- ( ph -> ( X + 1 ) e. A )


  assert |- ( ph -> ( ( _/_\ ` F ) ` X ) = ( ( F ` ( X + 1 ) ) - ( F ` X ) ) )

  proof
    wph
    vx
    cX
    vx
    cv
    #
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @0
    cF
    cfv
    #
    cmin
    co
    #
    cX
    c1
    caddc
    co
    #
    cF
    cfv
    #
    cX
    cF
    cfv
    #
    cmin
    co
    #
    vy
    cv
    #
    c1
    caddc
    co
    #
    cA
    wcel
    #
    vy
    cA
    crab
    #
    cF
    cfwddif
    cfv
    #
    cvv
    wph
    @13
    vx
    @10
    cF
    cdm
    #
    wcel
    #
    vy
    @14
    crab
    #
    @4
    cmpt
    #
    vx
    @12
    @4
    cmpt
    wph
    vf
    cF
    vx
    @10
    vf
    cv
    #
    cdm
    #
    wcel
    #
    vy
    @19
    crab
    #
    @1
    @18
    cfv
    #
    @0
    @18
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    @17
    cc
    cc
    cpm
    co
    #
    cfwddif
    cvv
    cfwddif
    vf
    @26
    @25
    cmpt
    wceq
    wph
    vx
    vy
    vf
    df-fwddif
    a1i
    @18
    cF
    wceq
    #
    @25
    @17
    wceq
    wph
    @27
    vx
    @21
    @24
    @16
    @4
    @27
    @20
    @15
    vy
    @19
    @14
    @18
    cF
    dmeq
    #
    @27
    @19
    @14
    @10
    @28
    eleq2d
    rabeqbidv
    @27
    @22
    @2
    @23
    @3
    cmin
    @1
    @18
    cF
    fveq1
    @0
    @18
    cF
    fveq1
    oveq12d
    mpteq12dv
    adantl
    wph
    cA
    cc
    cF
    wf
    #
    cA
    cc
    wss
    #
    cF
    @26
    wcel
    #
    fwddifval.2
    fwddifval.1
    cc
    cvv
    wcel
    #
    @32
    @29
    @30
    wa
    @31
    cnex
    cnex
    cc
    cc
    cA
    cF
    cvv
    cvv
    elpm2r
    mpanl12
    syl2anc
    wph
    @14
    cvv
    wcel
    @16
    cvv
    wcel
    @17
    cvv
    wcel
    wph
    @14
    cA
    cvv
    wph
    @29
    @14
    cA
    wceq
    fwddifval.2
    cA
    cc
    cF
    fdm
    syl
    #
    wph
    cA
    cc
    cvv
    @32
    wph
    cnex
    a1i
    fwddifval.1
    ssexd
    eqeltrd
    @15
    vy
    @14
    cvv
    rabexg
    vx
    @16
    @4
    cvv
    mptexg
    3syl
    fvmptd
    wph
    vx
    @16
    @12
    @4
    wph
    @15
    @11
    vy
    @14
    cA
    @33
    wph
    @14
    cA
    @10
    @33
    eleq2d
    rabeqbidv
    mpteq1d
    eqtrd
    @0
    cX
    wceq
    #
    @4
    @8
    wceq
    wph
    @34
    @2
    @6
    @3
    @7
    cmin
    @34
    @1
    @5
    cF
    @0
    cX
    c1
    caddc
    oveq1
    fveq2d
    @0
    cX
    cF
    fveq2
    oveq12d
    adantl
    wph
    cX
    cA
    wcel
    @5
    cA
    wcel
    #
    cX
    @12
    wcel
    fwddifval.3
    fwddifval.4
    @11
    @35
    vy
    cX
    cA
    @9
    cX
    wceq
    @10
    @5
    cA
    @9
    cX
    c1
    caddc
    oveq1
    eleq1d
    elrab
    sylanbrc
    wph
    @6
    @7
    cmin
    ovexd
    fvmptd
end
