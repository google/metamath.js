include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "cr.mm"
include "wf.mm"
include "cme.mm"
include "metxmet.mm"
include "syl.mm"
include "imasf1oxmet.mm"
include "wfn.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "cds.mm"
include "wf1o.mm"
include "wfo.mm"
include "f1ofo.mm"
include "eqid.mm"
include "imasdsfn.mm"
include "wa.mm"
include "cimas.mm"
include "wceq.mm"
include "adantr.mm"
include "cbs.mm"
include "simprl.mm"
include "simprr.mm"
include "imasdsf1o.mm"
include "metcl.mm"
include "3expb.mm"
include "sylan.mm"
include "eqeltrd.mm"
include "ralrimivva.mm"
include "crn.mm"
include "wb.mm"
include "f1ofn.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "ralrn.mm"
include "forn.mm"
include "raleqdv.mm"
include "bitr3d.mm"
include "ralbidv.mm"
include "mpbid.mm"
include "oveq1.mm"
include "ffnov.mm"
include "sylanbrc.mm"
include "ismet2.mm"

theorem imasf1omet
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let cU: class U
  let cE: class E
  let cF: class F
  let cV: class V
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vc: setvar c
  assume imasf1oxmet.u: |- ( ph -> U = ( F "s R ) )
  assume imasf1oxmet.v: |- ( ph -> V = ( Base ` R ) )
  assume imasf1oxmet.f: |- ( ph -> F : V -1-1-onto-> B )
  assume imasf1oxmet.r: |- ( ph -> R e. Z )
  assume imasf1oxmet.e: |- E = ( ( dist ` R ) |` ( V X. V ) )
  assume imasf1oxmet.d: |- D = ( dist ` U )
  assume imasf1omet.m: |- ( ph -> E e. ( Met ` V ) )


  assert |- ( ph -> D e. ( Met ` B ) )

  proof
    wph
    cD
    cB
    cxmt
    cfv
    wcel
    cB
    cB
    cxp
    #
    cr
    cD
    wf
    #
    cD
    cB
    cme
    cfv
    wcel
    wph
    cB
    cD
    cR
    cU
    cE
    cF
    cV
    cZ
    imasf1oxmet.u
    imasf1oxmet.v
    imasf1oxmet.f
    imasf1oxmet.r
    imasf1oxmet.e
    imasf1oxmet.d
    wph
    cE
    cV
    cme
    cfv
    wcel
    #
    cE
    cV
    cxmt
    cfv
    wcel
    #
    imasf1omet.m
    cE
    cV
    metxmet
    syl
    #
    imasf1oxmet
    wph
    cD
    @0
    wfn
    vx
    cv
    #
    vy
    cv
    #
    cD
    co
    #
    cr
    wcel
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    @1
    wph
    cB
    cD
    cR
    cU
    cR
    cds
    cfv
    #
    cF
    cV
    cZ
    imasf1oxmet.u
    imasf1oxmet.v
    wph
    cV
    cB
    cF
    wf1o
    #
    cV
    cB
    cF
    wfo
    #
    imasf1oxmet.f
    cV
    cB
    cF
    f1ofo
    syl
    #
    imasf1oxmet.r
    @11
    eqid
    imasf1oxmet.d
    imasdsfn
    wph
    va
    cv
    #
    cF
    cfv
    #
    @6
    cD
    co
    #
    cr
    wcel
    #
    vy
    cB
    wral
    #
    va
    cV
    wral
    #
    @10
    wph
    @16
    vb
    cv
    #
    cF
    cfv
    #
    cD
    co
    #
    cr
    wcel
    #
    vb
    cV
    wral
    #
    va
    cV
    wral
    @20
    wph
    @24
    va
    vb
    cV
    cV
    wph
    @15
    cV
    wcel
    #
    @21
    cV
    wcel
    #
    wa
    #
    wa
    #
    @23
    @15
    @21
    cE
    co
    #
    cr
    @29
    cB
    cD
    cR
    cU
    cE
    cF
    cV
    @15
    @21
    cZ
    wph
    cU
    cF
    cR
    cimas
    co
    wceq
    @28
    imasf1oxmet.u
    adantr
    wph
    cV
    cR
    cbs
    cfv
    wceq
    @28
    imasf1oxmet.v
    adantr
    wph
    @12
    @28
    imasf1oxmet.f
    adantr
    wph
    cR
    cZ
    wcel
    @28
    imasf1oxmet.r
    adantr
    imasf1oxmet.e
    imasf1oxmet.d
    wph
    @3
    @28
    @4
    adantr
    wph
    @26
    @27
    simprl
    wph
    @26
    @27
    simprr
    imasdsf1o
    wph
    @2
    @28
    @30
    cr
    wcel
    #
    imasf1omet.m
    @2
    @26
    @27
    @31
    @15
    @21
    cE
    cV
    metcl
    3expb
    sylan
    eqeltrd
    ralrimivva
    wph
    @25
    @19
    va
    cV
    wph
    @18
    vy
    cF
    crn
    #
    wral
    #
    @25
    @19
    wph
    cF
    cV
    wfn
    #
    @33
    @25
    wb
    wph
    @12
    @34
    imasf1oxmet.f
    cV
    cB
    cF
    f1ofn
    syl
    #
    @18
    @24
    vy
    vb
    cV
    cF
    @6
    @22
    wceq
    @17
    @23
    cr
    @6
    @22
    @16
    cD
    oveq2
    eleq1d
    ralrn
    syl
    wph
    @18
    vy
    @32
    cB
    wph
    @13
    @32
    cB
    wceq
    @14
    cV
    cB
    cF
    forn
    syl
    #
    raleqdv
    bitr3d
    ralbidv
    mpbid
    wph
    @9
    vx
    @32
    wral
    #
    @20
    @10
    wph
    @34
    @37
    @20
    wb
    @35
    @9
    @19
    vx
    va
    cV
    cF
    @5
    @16
    wceq
    #
    @8
    @18
    vy
    cB
    @38
    @7
    @17
    cr
    @5
    @16
    @6
    cD
    oveq1
    eleq1d
    ralbidv
    ralrn
    syl
    wph
    @9
    vx
    @32
    cB
    @36
    raleqdv
    bitr3d
    mpbid
    vx
    vy
    cB
    cB
    cr
    cD
    ffnov
    sylanbrc
    cD
    cB
    ismet2
    sylanbrc
end
