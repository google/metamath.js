include "ct0.mm"
include "wcel.mm"
include "wf1.mm"
include "ccn.mm"
include "co.mm"
include "w3a.mm"
include "ctop.mm"
include "cv.mm"
include "wb.mm"
include "wral.mm"
include "wceq.mm"
include "wi.mm"
include "cuni.mm"
include "cntop1.mm"
include "3ad2ant3.mm"
include "wa.mm"
include "cfv.mm"
include "ccnv.mm"
include "cima.mm"
include "simpl3.mm"
include "cnima.mm"
include "sylan.mm"
include "eleq2.mm"
include "bibi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "wfn.mm"
include "wf.mm"
include "eqid.mm"
include "cnf.mm"
include "ffn.mm"
include "elpreima.mm"
include "simprl.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "simprr.mm"
include "adantr.mm"
include "sylibd.mm"
include "ralrimdva.mm"
include "simpl1.mm"
include "ffvelrnd.mm"
include "t0sep.mm"
include "syl12anc.mm"
include "syld.mm"
include "simpl2.mm"
include "cdm.mm"
include "fdm.mm"
include "f1dm.mm"
include "eqtr3d.mm"
include "eleqtrd.mm"
include "f1fveq.mm"
include "ralrimivva.mm"
include "ist0.mm"
include "sylanbrc.mm"

theorem cnt0
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vm: setvar m
  let vn: setvar n
  let vc: setvar c
  let vd: setvar d
  let vj: setvar j
  let vo: setvar o
  let cU: class U
  let cV: class V


  assert |- ( ( K e. Kol2 /\ F : X -1-1-> Y /\ F e. ( J Cn K ) ) -> J e. Kol2 )

  proof
    cK
    ct0
    wcel
    #
    cX
    cY
    cF
    wf1
    #
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    w3a
    #
    cJ
    ctop
    wcel
    #
    vx
    cv
    #
    vz
    cv
    #
    wcel
    #
    vy
    cv
    #
    @6
    wcel
    #
    wb
    #
    vz
    cJ
    wral
    #
    @5
    @8
    wceq
    #
    wi
    #
    vy
    cJ
    cuni
    #
    wral
    vx
    @14
    wral
    cJ
    ct0
    wcel
    @2
    @0
    @4
    @1
    cF
    cJ
    cK
    cntop1
    3ad2ant3
    @3
    @13
    vx
    vy
    @14
    @14
    @3
    @5
    @14
    wcel
    #
    @8
    @14
    wcel
    #
    wa
    #
    wa
    #
    @11
    @5
    cF
    cfv
    #
    @8
    cF
    cfv
    #
    wceq
    #
    @12
    @18
    @11
    @19
    vw
    cv
    #
    wcel
    #
    @20
    @22
    wcel
    #
    wb
    #
    vw
    cK
    wral
    #
    @21
    @18
    @11
    @25
    vw
    cK
    @18
    @22
    cK
    wcel
    #
    wa
    #
    @11
    @5
    cF
    ccnv
    @22
    cima
    #
    wcel
    #
    @8
    @29
    wcel
    #
    wb
    #
    @25
    @28
    @29
    cJ
    wcel
    #
    @11
    @32
    wi
    @18
    @2
    @27
    @33
    @0
    @1
    @2
    @17
    simpl3
    #
    @22
    cF
    cJ
    cK
    cnima
    sylan
    @10
    @32
    vz
    @29
    cJ
    @6
    @29
    wceq
    @7
    @30
    @9
    @31
    @6
    @29
    @5
    eleq2
    @6
    @29
    @8
    eleq2
    bibi12d
    rspcv
    syl
    @18
    @32
    @25
    wb
    @27
    @18
    @30
    @23
    @31
    @24
    @18
    @30
    @15
    @23
    wa
    #
    @23
    @18
    cF
    @14
    wfn
    #
    @30
    @35
    wb
    @18
    @14
    cK
    cuni
    #
    cF
    wf
    #
    @36
    @18
    @2
    @38
    @34
    cF
    cJ
    cK
    @14
    @37
    @14
    eqid
    #
    @37
    eqid
    #
    cnf
    syl
    #
    @14
    @37
    cF
    ffn
    syl
    #
    @14
    @5
    @22
    cF
    elpreima
    syl
    @18
    @15
    @23
    @3
    @15
    @16
    simprl
    #
    biantrurd
    bitr4d
    @18
    @31
    @16
    @24
    wa
    #
    @24
    @18
    @36
    @31
    @44
    wb
    @42
    @14
    @8
    @22
    cF
    elpreima
    syl
    @18
    @16
    @24
    @3
    @15
    @16
    simprr
    #
    biantrurd
    bitr4d
    bibi12d
    adantr
    sylibd
    ralrimdva
    @18
    @0
    @19
    @37
    wcel
    @20
    @37
    wcel
    @26
    @21
    wi
    @0
    @1
    @2
    @17
    simpl1
    @18
    @14
    @37
    @5
    cF
    @41
    @43
    ffvelrnd
    @18
    @14
    @37
    @8
    cF
    @41
    @45
    ffvelrnd
    vw
    @19
    @20
    cK
    @37
    @40
    t0sep
    syl12anc
    syld
    @18
    @1
    @5
    cX
    wcel
    @8
    cX
    wcel
    @21
    @12
    wb
    @0
    @1
    @2
    @17
    simpl2
    #
    @18
    @5
    @14
    cX
    @43
    @18
    cF
    cdm
    #
    @14
    cX
    @18
    @38
    @47
    @14
    wceq
    @41
    @14
    @37
    cF
    fdm
    syl
    @18
    @1
    @47
    cX
    wceq
    @46
    cX
    cY
    cF
    f1dm
    syl
    eqtr3d
    #
    eleqtrd
    @18
    @8
    @14
    cX
    @45
    @48
    eleqtrd
    cX
    cY
    @5
    @8
    cF
    f1fveq
    syl12anc
    sylibd
    ralrimivva
    vx
    vy
    vz
    cJ
    @14
    @39
    ist0
    sylanbrc
end
