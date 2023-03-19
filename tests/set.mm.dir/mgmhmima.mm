include "cmgmhm.mm"
include "co.mm"
include "wcel.mm"
include "csubmgm.mm"
include "cfv.mm"
include "wa.mm"
include "cima.mm"
include "cbs.mm"
include "wss.mm"
include "cv.mm"
include "cplusg.mm"
include "wral.mm"
include "crn.mm"
include "imassrn.mm"
include "wf.mm"
include "eqid.mm"
include "mgmhmf.mm"
include "adantr.mm"
include "frn.mm"
include "syl.mm"
include "syl5ss.mm"
include "wceq.mm"
include "simpll.mm"
include "submgmss.mm"
include "adantl.mm"
include "simprl.mm"
include "sseldd.mm"
include "simprr.mm"
include "mgmhmlin.mm"
include "syl3anc.mm"
include "wfn.mm"
include "ffn.mm"
include "submgmcl.mm"
include "3expb.mm"
include "adantll.mm"
include "fnfvima.mm"
include "eqeltrrd.mm"
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
include "cmgm.mm"
include "mgmhmrcl.mm"
include "simprd.mm"
include "issubmgm.mm"
include "mpbir2and.mm"

theorem mgmhmima
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k


  assert |- ( ( F e. ( M MgmHom N ) /\ X e. ( SubMgm ` M ) ) -> ( F " X ) e. ( SubMgm ` N ) )

  proof
    cF
    cM
    cN
    cmgmhm
    co
    wcel
    #
    cX
    cM
    csubmgm
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
    csubmgm
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
    @14
    @5
    wss
    @0
    @16
    @1
    @15
    @5
    cM
    cN
    cF
    @15
    eqid
    #
    @5
    eqid
    #
    mgmhmf
    adantr
    #
    @15
    @5
    cF
    frn
    syl
    syl5ss
    @2
    @13
    vz
    cv
    #
    cF
    cfv
    #
    @8
    @9
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
    @24
    vz
    cX
    @2
    @20
    cX
    wcel
    #
    wa
    #
    @24
    @21
    @7
    cF
    cfv
    #
    @9
    co
    #
    @3
    wcel
    #
    vx
    cX
    wral
    #
    @27
    @30
    vx
    cX
    @2
    @26
    @7
    cX
    wcel
    #
    @30
    @2
    @26
    @32
    wa
    #
    wa
    #
    @20
    @7
    cM
    cplusg
    cfv
    #
    co
    #
    cF
    cfv
    #
    @29
    @3
    @34
    @0
    @20
    @15
    wcel
    @7
    @15
    wcel
    @37
    @29
    wceq
    @0
    @1
    @33
    simpll
    @34
    cX
    @15
    @20
    @2
    cX
    @15
    wss
    #
    @33
    @1
    @38
    @0
    @15
    cX
    cM
    @17
    submgmss
    adantl
    #
    adantr
    #
    @2
    @26
    @32
    simprl
    sseldd
    @34
    cX
    @15
    @7
    @40
    @2
    @26
    @32
    simprr
    sseldd
    @15
    @35
    @9
    cM
    cN
    cF
    @20
    @7
    @17
    @35
    eqid
    #
    @9
    eqid
    #
    mgmhmlin
    syl3anc
    @34
    cF
    @15
    wfn
    #
    @38
    @36
    cX
    wcel
    #
    @37
    @3
    wcel
    @2
    @43
    @33
    @2
    @16
    @43
    @19
    @15
    @5
    cF
    ffn
    syl
    #
    adantr
    @40
    @1
    @33
    @44
    @0
    @1
    @26
    @32
    @44
    @35
    cX
    cM
    @20
    @7
    @41
    submgmcl
    3expb
    adantll
    @15
    cX
    cF
    @36
    fnfvima
    syl3anc
    eqeltrrd
    anassrs
    ralrimiva
    @2
    @24
    @31
    wb
    #
    @26
    @2
    @43
    @38
    @46
    @45
    @39
    @23
    @30
    vy
    vx
    @15
    cX
    cF
    @8
    @28
    wceq
    @22
    @29
    @3
    @8
    @28
    @21
    @9
    oveq2
    eleq1d
    ralima
    syl2anc
    adantr
    mpbird
    ralrimiva
    @2
    @43
    @38
    @13
    @25
    wb
    @45
    @39
    @12
    @24
    vx
    vz
    @15
    cX
    cF
    @7
    @21
    wceq
    #
    @11
    @23
    vy
    @3
    @47
    @10
    @22
    @3
    @7
    @21
    @8
    @9
    oveq1
    eleq1d
    ralbidv
    ralima
    syl2anc
    mpbird
    @2
    cN
    cmgm
    wcel
    #
    @4
    @6
    @13
    wa
    wb
    @0
    @48
    @1
    @0
    cM
    cmgm
    wcel
    @48
    cM
    cN
    cF
    mgmhmrcl
    simprd
    adantr
    vx
    vy
    @5
    @9
    @3
    cN
    @18
    @42
    issubmgm
    syl
    mpbir2and
end
