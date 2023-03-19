include "cmhm.mm"
include "co.mm"
include "wcel.mm"
include "csubmnd.mm"
include "cfv.mm"
include "wa.mm"
include "cima.mm"
include "cbs.mm"
include "wss.mm"
include "c0g.mm"
include "cv.mm"
include "cplusg.mm"
include "wral.mm"
include "crn.mm"
include "imassrn.mm"
include "wf.mm"
include "eqid.mm"
include "mhmf.mm"
include "adantr.mm"
include "frn.mm"
include "syl.mm"
include "syl5ss.mm"
include "wceq.mm"
include "mhm0.mm"
include "wfn.mm"
include "ffn.mm"
include "submss.mm"
include "adantl.mm"
include "subm0cl.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "simpll.mm"
include "simprl.mm"
include "sseldd.mm"
include "simprr.mm"
include "mhmlin.mm"
include "submcl.mm"
include "3expb.mm"
include "adantll.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "wb.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "ralima.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "oveq1.mm"
include "ralbidv.mm"
include "cmnd.mm"
include "w3a.mm"
include "mhmrcl2.mm"
include "issubm.mm"
include "mpbir3and.mm"

theorem mhmima
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( F e. ( M MndHom N ) /\ X e. ( SubMnd ` M ) ) -> ( F " X ) e. ( SubMnd ` N ) )

  proof
    cF
    cM
    cN
    cmhm
    co
    wcel
    #
    cX
    cM
    csubmnd
    cfv
    wcel
    #
    wa
    #
    cF
    cX
    cima
    #
    cN
    csubmnd
    cfv
    wcel
    #
    @3
    cN
    cbs
    cfv
    #
    wss
    #
    cN
    c0g
    cfv
    #
    @3
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cN
    cplusg
    cfv
    #
    co
    #
    @3
    wcel
    #
    vy
    @3
    wral
    #
    vx
    @3
    wral
    #
    @2
    @3
    cF
    crn
    #
    @5
    cF
    cX
    imassrn
    @2
    cM
    cbs
    cfv
    #
    @5
    cF
    wf
    #
    @16
    @5
    wss
    @0
    @18
    @1
    @17
    @5
    cM
    cN
    cF
    @17
    eqid
    #
    @5
    eqid
    #
    mhmf
    adantr
    #
    @17
    @5
    cF
    frn
    syl
    syl5ss
    @2
    cM
    c0g
    cfv
    #
    cF
    cfv
    #
    @7
    @3
    @0
    @23
    @7
    wceq
    @1
    cM
    cN
    cF
    @7
    @22
    @22
    eqid
    #
    @7
    eqid
    #
    mhm0
    adantr
    @2
    cF
    @17
    wfn
    #
    cX
    @17
    wss
    #
    @22
    cX
    wcel
    #
    @23
    @3
    wcel
    @2
    @18
    @26
    @21
    @17
    @5
    cF
    ffn
    syl
    #
    @1
    @27
    @0
    @17
    cX
    cM
    @19
    submss
    adantl
    #
    @1
    @28
    @0
    cX
    cM
    @22
    @24
    subm0cl
    adantl
    @17
    cX
    cF
    @22
    fnfvima
    syl3anc
    eqeltrrd
    @2
    @15
    vz
    cv
    #
    cF
    cfv
    #
    @10
    @11
    co
    #
    @3
    wcel
    #
    vy
    @3
    wral
    #
    vz
    cX
    wral
    #
    @2
    @35
    vz
    cX
    @2
    @31
    cX
    wcel
    #
    wa
    #
    @35
    @32
    @9
    cF
    cfv
    #
    @11
    co
    #
    @3
    wcel
    #
    vx
    cX
    wral
    #
    @38
    @41
    vx
    cX
    @2
    @37
    @9
    cX
    wcel
    #
    @41
    @2
    @37
    @43
    wa
    #
    wa
    #
    @31
    @9
    cM
    cplusg
    cfv
    #
    co
    #
    cF
    cfv
    #
    @40
    @3
    @45
    @0
    @31
    @17
    wcel
    @9
    @17
    wcel
    @48
    @40
    wceq
    @0
    @1
    @44
    simpll
    @45
    cX
    @17
    @31
    @2
    @27
    @44
    @30
    adantr
    #
    @2
    @37
    @43
    simprl
    sseldd
    @45
    cX
    @17
    @9
    @49
    @2
    @37
    @43
    simprr
    sseldd
    @17
    @46
    @11
    cM
    cN
    cF
    @31
    @9
    @19
    @46
    eqid
    #
    @11
    eqid
    #
    mhmlin
    syl3anc
    @45
    @26
    @27
    @47
    cX
    wcel
    #
    @48
    @3
    wcel
    @2
    @26
    @44
    @29
    adantr
    @49
    @1
    @44
    @52
    @0
    @1
    @37
    @43
    @52
    @46
    cX
    cM
    @31
    @9
    @50
    submcl
    3expb
    adantll
    @17
    cX
    cF
    @47
    fnfvima
    syl3anc
    eqeltrrd
    anassrs
    ralrimiva
    @2
    @35
    @42
    wb
    #
    @37
    @2
    @26
    @27
    @53
    @29
    @30
    @34
    @41
    vy
    vx
    @17
    cX
    cF
    @10
    @39
    wceq
    @33
    @40
    @3
    @10
    @39
    @32
    @11
    oveq2
    eleq1d
    ralima
    syl2anc
    adantr
    mpbird
    ralrimiva
    @2
    @26
    @27
    @15
    @36
    wb
    @29
    @30
    @14
    @35
    vx
    vz
    @17
    cX
    cF
    @9
    @32
    wceq
    #
    @13
    @34
    vy
    @3
    @54
    @12
    @33
    @3
    @9
    @32
    @10
    @11
    oveq1
    eleq1d
    ralbidv
    ralima
    syl2anc
    mpbird
    @2
    cN
    cmnd
    wcel
    #
    @4
    @6
    @8
    @15
    w3a
    wb
    @0
    @55
    @1
    cM
    cN
    cF
    mhmrcl2
    adantr
    vx
    vy
    @5
    @11
    @3
    cN
    @7
    @20
    @25
    @51
    issubm
    syl
    mpbir3and
end
