include "cv.mm"
include "csb.mm"
include "wcel.mm"
include "crab.mm"
include "cwdom.mm"
include "wbr.mm"
include "cmpt.mm"
include "cvv.mm"
include "wfo.mm"
include "cxp.mm"
include "rabexg.mm"
include "syl.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "wf.mm"
include "wss.mm"
include "wceq.mm"
include "csbeq1.mm"
include "eleq1d.mm"
include "elrab.mm"
include "simprbi.mm"
include "adantl.mm"
include "eqid.mm"
include "fmptd.mm"
include "fssxp.mm"
include "ssexd.mm"
include "cfv.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "wi.mm"
include "eleq1.mm"
include "biimpcd.mm"
include "ancrd.mm"
include "reximdv.mm"
include "mpd.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "nfeq2.mm"
include "nfan.mm"
include "csbeq1a.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "cbvrex.mm"
include "sylib.mm"
include "fvmptg.mm"
include "mpdan.mm"
include "rexbiia.mm"
include "rexrab.mm"
include "bitri.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "sylanbrc.mm"
include "fowdom.mm"
include "cdom.mm"
include "ssrab2.mm"
include "ssdomg.mm"
include "mpi.mm"
include "domwdom.mm"
include "3syl.mm"
include "wdomtr.mm"

theorem wdom2d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let cX: class X
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume wdom2d.a: |- ( ph -> A e. V )
  assume wdom2d.b: |- ( ph -> B e. W )
  assume wdom2d.o: |- ( ( ph /\ x e. A ) -> E. y e. B x = X )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint X x
  disjoint ph x
  disjoint ph y
  disjoint A v
  disjoint A w
  disjoint A z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint B v
  disjoint B w
  disjoint B z
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint ph w
  assert |- ( ph -> A ~<_* B )

  proof
    wph
    cA
    vy
    vz
    cv
    #
    cX
    csb
    #
    cA
    wcel
    #
    vz
    cB
    crab
    #
    cwdom
    wbr
    #
    @3
    cB
    cwdom
    wbr
    #
    cA
    cB
    cwdom
    wbr
    wph
    vw
    @3
    vy
    vw
    cv
    #
    cX
    csb
    #
    cmpt
    #
    cvv
    wcel
    @3
    cA
    @8
    wfo
    #
    @4
    wph
    @8
    @3
    cA
    cxp
    #
    cvv
    wph
    @3
    cvv
    wcel
    #
    cA
    cV
    wcel
    @10
    cvv
    wcel
    wph
    cB
    cW
    wcel
    #
    @11
    wdom2d.b
    @2
    vz
    cB
    cW
    rabexg
    syl
    wdom2d.a
    @3
    cA
    cvv
    cV
    xpexg
    syl2anc
    wph
    @3
    cA
    @8
    wf
    #
    @8
    @10
    wss
    wph
    vw
    @3
    @7
    cA
    @8
    @6
    @3
    wcel
    #
    @7
    cA
    wcel
    #
    wph
    @14
    @6
    cB
    wcel
    @15
    @2
    @15
    vz
    @6
    cB
    @0
    @6
    wceq
    @1
    @7
    cA
    vy
    @0
    @6
    cX
    csbeq1
    eleq1d
    elrab
    simprbi
    adantl
    @8
    eqid
    #
    fmptd
    #
    @3
    cA
    @8
    fssxp
    syl
    ssexd
    wph
    @13
    vx
    cv
    #
    vv
    cv
    #
    @8
    cfv
    #
    wceq
    #
    vv
    @3
    wrex
    #
    vx
    cA
    wral
    @9
    @17
    wph
    @22
    vx
    cA
    wph
    @18
    cA
    wcel
    #
    wa
    #
    vy
    @19
    cX
    csb
    #
    cA
    wcel
    #
    @18
    @25
    wceq
    #
    wa
    #
    vv
    cB
    wrex
    #
    @22
    @24
    cX
    cA
    wcel
    #
    @18
    cX
    wceq
    #
    wa
    #
    vy
    cB
    wrex
    #
    @29
    @24
    @31
    vy
    cB
    wrex
    @33
    wdom2d.o
    @24
    @31
    @32
    vy
    cB
    @23
    @31
    @32
    wi
    wph
    @23
    @31
    @30
    @31
    @23
    @30
    @18
    cX
    cA
    eleq1
    biimpcd
    ancrd
    adantl
    reximdv
    mpd
    @32
    @28
    vy
    vv
    cB
    @32
    vv
    nfv
    @26
    @27
    vy
    vy
    @25
    cA
    vy
    @19
    cX
    nfcsb1v
    #
    nfel1
    vy
    @18
    @25
    @34
    nfeq2
    nfan
    vy
    cv
    @19
    wceq
    #
    @30
    @26
    @31
    @27
    @35
    cX
    @25
    cA
    vy
    @19
    cX
    csbeq1a
    #
    eleq1d
    @35
    cX
    @25
    @18
    @36
    eqeq2d
    anbi12d
    cbvrex
    sylib
    @22
    @27
    vv
    @3
    wrex
    @29
    @21
    @27
    vv
    @3
    @19
    @3
    wcel
    #
    @20
    @25
    @18
    @37
    @26
    @20
    @25
    wceq
    @37
    @19
    cB
    wcel
    @26
    @2
    @26
    vz
    @19
    cB
    @0
    @19
    wceq
    @1
    @25
    cA
    vy
    @0
    @19
    cX
    csbeq1
    eleq1d
    #
    elrab
    simprbi
    vw
    @19
    @7
    @25
    @3
    cA
    @8
    vy
    @6
    @19
    cX
    csbeq1
    @16
    fvmptg
    mpdan
    eqeq2d
    rexbiia
    @2
    @26
    @27
    vv
    vz
    cB
    @38
    rexrab
    bitri
    sylibr
    ralrimiva
    vv
    vx
    @3
    cA
    @8
    dffo3
    sylanbrc
    @8
    cvv
    cA
    @3
    fowdom
    syl2anc
    wph
    @12
    @3
    cB
    cdom
    wbr
    #
    @5
    wdom2d.b
    @12
    @3
    cB
    wss
    @39
    @2
    vz
    cB
    ssrab2
    @3
    cB
    cW
    ssdomg
    mpi
    @3
    cB
    domwdom
    3syl
    cA
    @3
    cB
    wdomtr
    syl2anc
end
