include "cmhm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cin.mm"
include "cdm.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "crab.mm"
include "csubmnd.mm"
include "wfn.mm"
include "wf.mm"
include "eqid.mm"
include "mhmf.mm"
include "adantr.mm"
include "ffn.mm"
include "syl.mm"
include "adantl.mm"
include "fndmin.mm"
include "syl2anc.mm"
include "wss.mm"
include "c0g.mm"
include "cplusg.mm"
include "wral.mm"
include "ssrab2.mm"
include "a1i.mm"
include "cmnd.mm"
include "mhmrcl1.mm"
include "mndidcl.mm"
include "mhm0.mm"
include "eqtr4d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "wi.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "simprl.mm"
include "mndcl.mm"
include "syl3anc.mm"
include "simplll.mm"
include "mhmlin.mm"
include "simpllr.mm"
include "simplrr.mm"
include "simprr.mm"
include "oveq12d.mm"
include "expr.mm"
include "ralrimiva.mm"
include "ralrab.mm"
include "sylibr.mm"
include "w3a.mm"
include "wb.mm"
include "issubm.mm"
include "mpbir3and.mm"
include "eqeltrd.mm"

theorem mhmeql
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( F e. ( S MndHom T ) /\ G e. ( S MndHom T ) ) -> dom ( F i^i G ) e. ( SubMnd ` S ) )

  proof
    cF
    cS
    cT
    cmhm
    co
    #
    wcel
    #
    cG
    @0
    wcel
    #
    wa
    #
    cF
    cG
    cin
    cdm
    #
    vz
    cv
    #
    cF
    cfv
    #
    @5
    cG
    cfv
    #
    wceq
    #
    vz
    cS
    cbs
    cfv
    #
    crab
    #
    cS
    csubmnd
    cfv
    #
    @3
    cF
    @9
    wfn
    #
    cG
    @9
    wfn
    #
    @4
    @10
    wceq
    @3
    @9
    cT
    cbs
    cfv
    #
    cF
    wf
    #
    @12
    @1
    @15
    @2
    @9
    @14
    cS
    cT
    cF
    @9
    eqid
    #
    @14
    eqid
    #
    mhmf
    adantr
    @9
    @14
    cF
    ffn
    syl
    @3
    @9
    @14
    cG
    wf
    #
    @13
    @2
    @18
    @1
    @9
    @14
    cS
    cT
    cG
    @16
    @17
    mhmf
    adantl
    @9
    @14
    cG
    ffn
    syl
    vz
    @9
    cF
    cG
    fndmin
    syl2anc
    @3
    @10
    @11
    wcel
    #
    @10
    @9
    wss
    #
    cS
    c0g
    cfv
    #
    @10
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cS
    cplusg
    cfv
    #
    co
    #
    @10
    wcel
    #
    vy
    @10
    wral
    #
    vx
    @10
    wral
    #
    @20
    @3
    @8
    vz
    @9
    ssrab2
    a1i
    @3
    @21
    @9
    wcel
    #
    @21
    cF
    cfv
    #
    @21
    cG
    cfv
    #
    wceq
    #
    @22
    @3
    cS
    cmnd
    wcel
    #
    @30
    @1
    @34
    @2
    cS
    cT
    cF
    mhmrcl1
    adantr
    #
    @9
    cS
    @21
    @16
    @21
    eqid
    #
    mndidcl
    syl
    @3
    @31
    cT
    c0g
    cfv
    #
    @32
    @1
    @31
    @37
    wceq
    @2
    cS
    cT
    cF
    @37
    @21
    @36
    @37
    eqid
    #
    mhm0
    adantr
    @2
    @32
    @37
    wceq
    @1
    cS
    cT
    cG
    @37
    @21
    @36
    @38
    mhm0
    adantl
    eqtr4d
    @8
    @33
    vz
    @21
    @9
    @5
    @21
    wceq
    @6
    @31
    @7
    @32
    @5
    @21
    cF
    fveq2
    @5
    @21
    cG
    fveq2
    eqeq12d
    elrab
    sylanbrc
    @3
    @23
    cF
    cfv
    #
    @23
    cG
    cfv
    #
    wceq
    #
    @28
    wi
    #
    vx
    @9
    wral
    @29
    @3
    @42
    vx
    @9
    @3
    @23
    @9
    wcel
    #
    @41
    @28
    @3
    @43
    @41
    wa
    #
    wa
    #
    @24
    cF
    cfv
    #
    @24
    cG
    cfv
    #
    wceq
    #
    @27
    wi
    #
    vy
    @9
    wral
    @28
    @45
    @49
    vy
    @9
    @45
    @24
    @9
    wcel
    #
    @48
    @27
    @45
    @50
    @48
    wa
    #
    wa
    #
    @26
    @9
    wcel
    #
    @26
    cF
    cfv
    #
    @26
    cG
    cfv
    #
    wceq
    #
    @27
    @52
    @34
    @43
    @50
    @53
    @3
    @34
    @44
    @51
    @35
    ad2antrr
    @3
    @43
    @41
    @51
    simplrl
    #
    @45
    @50
    @48
    simprl
    #
    @9
    @25
    cS
    @23
    @24
    @16
    @25
    eqid
    #
    mndcl
    syl3anc
    @52
    @54
    @39
    @46
    cT
    cplusg
    cfv
    #
    co
    #
    @55
    @52
    @1
    @43
    @50
    @54
    @61
    wceq
    @1
    @2
    @44
    @51
    simplll
    @57
    @58
    @9
    @25
    @60
    cS
    cT
    cF
    @23
    @24
    @16
    @59
    @60
    eqid
    #
    mhmlin
    syl3anc
    @52
    @55
    @40
    @47
    @60
    co
    #
    @61
    @52
    @2
    @43
    @50
    @55
    @63
    wceq
    @1
    @2
    @44
    @51
    simpllr
    @57
    @58
    @9
    @25
    @60
    cS
    cT
    cG
    @23
    @24
    @16
    @59
    @62
    mhmlin
    syl3anc
    @52
    @39
    @40
    @46
    @47
    @60
    @3
    @43
    @41
    @51
    simplrr
    @45
    @50
    @48
    simprr
    oveq12d
    eqtr4d
    eqtr4d
    @8
    @56
    vz
    @26
    @9
    @5
    @26
    wceq
    @6
    @54
    @7
    @55
    @5
    @26
    cF
    fveq2
    @5
    @26
    cG
    fveq2
    eqeq12d
    elrab
    sylanbrc
    expr
    ralrimiva
    @8
    @48
    @27
    vy
    vz
    @9
    @5
    @24
    wceq
    @6
    @46
    @7
    @47
    @5
    @24
    cF
    fveq2
    @5
    @24
    cG
    fveq2
    eqeq12d
    ralrab
    sylibr
    expr
    ralrimiva
    @8
    @41
    @28
    vx
    vz
    @9
    @5
    @23
    wceq
    @6
    @39
    @7
    @40
    @5
    @23
    cF
    fveq2
    @5
    @23
    cG
    fveq2
    eqeq12d
    ralrab
    sylibr
    @3
    @34
    @19
    @20
    @22
    @29
    w3a
    wb
    @35
    vx
    vy
    @9
    @25
    @10
    cS
    @21
    @16
    @36
    @59
    issubm
    syl
    mpbir3and
    eqeltrd
end
