include "ctop.mm"
include "wcel.mm"
include "wf.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "ccnp.mm"
include "co.mm"
include "cfv.mm"
include "crest.mm"
include "wi.mm"
include "cnptop1.mm"
include "cnprcl.mm"
include "jca.mm"
include "a1i.mm"
include "wb.mm"
include "cv.mm"
include "cima.mm"
include "wrex.mm"
include "wral.mm"
include "cin.mm"
include "simpl2.mm"
include "simprr.mm"
include "ffvelrnd.mm"
include "biantrud.mm"
include "elin.mm"
include "syl6bbr.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "syl.mm"
include "syl5ss.mm"
include "ssin.mm"
include "syl6bb.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "cvv.mm"
include "vex.mm"
include "inex1.mm"
include "wceq.mm"
include "simpl1.mm"
include "cuni.mm"
include "uniexg.mm"
include "syl5eqel.mm"
include "simpl3.mm"
include "ssexd.mm"
include "elrest.mm"
include "syl2anc.mm"
include "eleq2.mm"
include "sseq2.mm"
include "adantl.mm"
include "ralxfr2d.mm"
include "bitr4d.mm"
include "simprl.mm"
include "iscnp2.mm"
include "baib.mm"
include "syl3anc.mm"
include "fssd.mm"
include "biantrurd.mm"
include "ctopon.mm"
include "toptopon.mm"
include "sylib.mm"
include "resttopon.mm"
include "iscnp.mm"
include "3bitr4d.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem cnprest2
  let cB: class B
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  assume cnprest.1: |- X = U. J
  assume cnprest.2: |- Y = U. K


  assert |- ( ( K e. Top /\ F : X --> B /\ B C_ Y ) -> ( F e. ( ( J CnP K ) ` P ) <-> F e. ( ( J CnP ( K |`t B ) ) ` P ) ) )

  proof
    cK
    ctop
    wcel
    #
    cX
    cB
    cF
    wf
    #
    cB
    cY
    wss
    #
    w3a
    #
    cJ
    ctop
    wcel
    #
    cP
    cX
    wcel
    #
    wa
    #
    cF
    cP
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    cF
    cP
    cJ
    cK
    cB
    crest
    co
    #
    ccnp
    co
    cfv
    wcel
    #
    @7
    @6
    wi
    @3
    @7
    @4
    @5
    cP
    cF
    cJ
    cK
    cnptop1
    cP
    cF
    cJ
    cK
    cX
    cnprest.1
    cnprcl
    jca
    a1i
    @9
    @6
    wi
    @3
    @9
    @4
    @5
    cP
    cF
    cJ
    @8
    cnptop1
    cP
    cF
    cJ
    @8
    cX
    cnprest.1
    cnprcl
    jca
    a1i
    @3
    @6
    @7
    @9
    wb
    @3
    @6
    wa
    #
    cP
    cF
    cfv
    #
    vx
    cv
    #
    wcel
    #
    cP
    vy
    cv
    #
    wcel
    #
    cF
    @14
    cima
    #
    @12
    wss
    #
    wa
    #
    vy
    cJ
    wrex
    #
    wi
    #
    vx
    cK
    wral
    #
    @11
    vz
    cv
    #
    wcel
    #
    @15
    @16
    @22
    wss
    #
    wa
    #
    vy
    cJ
    wrex
    #
    wi
    #
    vz
    @8
    wral
    #
    @7
    @9
    @10
    @21
    @11
    @12
    cB
    cin
    #
    wcel
    #
    @15
    @16
    @29
    wss
    #
    wa
    #
    vy
    cJ
    wrex
    #
    wi
    #
    vx
    cK
    wral
    @28
    @10
    @20
    @34
    vx
    cK
    @10
    @13
    @30
    @19
    @33
    @10
    @13
    @13
    @11
    cB
    wcel
    #
    wa
    @30
    @10
    @35
    @13
    @10
    cX
    cB
    cP
    cF
    @0
    @1
    @2
    @6
    simpl2
    #
    @3
    @4
    @5
    simprr
    #
    ffvelrnd
    biantrud
    @11
    @12
    cB
    elin
    syl6bbr
    @10
    @18
    @32
    vy
    cJ
    @10
    @17
    @31
    @15
    @10
    @17
    @17
    @16
    cB
    wss
    #
    wa
    @31
    @10
    @38
    @17
    @10
    @16
    cF
    crn
    #
    cB
    cF
    @14
    imassrn
    @10
    @1
    @39
    cB
    wss
    @36
    cX
    cB
    cF
    frn
    syl
    syl5ss
    biantrud
    @16
    @12
    cB
    ssin
    syl6bb
    anbi2d
    rexbidv
    imbi12d
    ralbidv
    @10
    @27
    @34
    vz
    vx
    @29
    @8
    cK
    cvv
    @29
    cvv
    wcel
    @10
    @12
    cK
    wcel
    wa
    @12
    cB
    vx
    vex
    inex1
    a1i
    @10
    @0
    cB
    cvv
    wcel
    @22
    @8
    wcel
    @22
    @29
    wceq
    #
    vx
    cK
    wrex
    wb
    @0
    @1
    @2
    @6
    simpl1
    #
    @10
    cB
    cY
    cvv
    @10
    @0
    cY
    cvv
    wcel
    @41
    @0
    cY
    cK
    cuni
    cvv
    cnprest.2
    cK
    ctop
    uniexg
    syl5eqel
    syl
    @0
    @1
    @2
    @6
    simpl3
    #
    ssexd
    vx
    @22
    cB
    cK
    ctop
    cvv
    elrest
    syl2anc
    @40
    @27
    @34
    wb
    @10
    @40
    @23
    @30
    @26
    @33
    @22
    @29
    @11
    eleq2
    @40
    @25
    @32
    vy
    cJ
    @40
    @24
    @31
    @15
    @22
    @29
    @16
    sseq2
    anbi2d
    rexbidv
    imbi12d
    adantl
    ralxfr2d
    bitr4d
    @10
    @7
    cX
    cY
    cF
    wf
    #
    @21
    wa
    #
    @21
    @10
    @4
    @0
    @5
    @7
    @44
    wb
    @3
    @4
    @5
    simprl
    #
    @41
    @37
    @7
    @4
    @0
    @5
    w3a
    @44
    vy
    vx
    cP
    cF
    cJ
    cK
    cX
    cY
    cnprest.1
    cnprest.2
    iscnp2
    baib
    syl3anc
    @10
    @43
    @21
    @10
    cX
    cB
    cY
    cF
    @36
    @42
    fssd
    biantrurd
    bitr4d
    @10
    @9
    @1
    @28
    wa
    #
    @28
    @10
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @8
    cB
    ctopon
    cfv
    wcel
    #
    @5
    @9
    @46
    wb
    @10
    @4
    @47
    @45
    cJ
    cX
    cnprest.1
    toptopon
    sylib
    @10
    cK
    cY
    ctopon
    cfv
    wcel
    #
    @2
    @48
    @10
    @0
    @49
    @41
    cK
    cY
    cnprest.2
    toptopon
    sylib
    @42
    cB
    cK
    cY
    resttopon
    syl2anc
    @37
    vy
    vz
    cP
    cF
    cJ
    @8
    cX
    cB
    iscnp
    syl3anc
    @10
    @1
    @28
    @36
    biantrurd
    bitr4d
    3bitr4d
    ex
    pm5.21ndd
end
