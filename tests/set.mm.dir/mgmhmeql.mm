include "cmgmhm.mm"
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
include "csubmgm.mm"
include "wfn.mm"
include "wf.mm"
include "eqid.mm"
include "mgmhmf.mm"
include "adantr.mm"
include "ffn.mm"
include "syl.mm"
include "adantl.mm"
include "fndmin.mm"
include "syl2anc.mm"
include "wss.mm"
include "cplusg.mm"
include "wral.mm"
include "ssrab2.mm"
include "a1i.mm"
include "wi.mm"
include "cmgm.mm"
include "mgmhmrcl.mm"
include "simpld.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "simprl.mm"
include "mgmcl.mm"
include "syl3anc.mm"
include "simplrr.mm"
include "simprr.mm"
include "oveq12d.mm"
include "simplll.mm"
include "mgmhmlin.mm"
include "simpllr.mm"
include "3eqtr4d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "expr.mm"
include "ralrimiva.mm"
include "ralrab.mm"
include "sylibr.mm"
include "wb.mm"
include "issubmgm.mm"
include "mpbir2and.mm"
include "eqeltrd.mm"

theorem mgmhmeql
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k


  assert |- ( ( F e. ( S MgmHom T ) /\ G e. ( S MgmHom T ) ) -> dom ( F i^i G ) e. ( SubMgm ` S ) )

  proof
    cF
    cS
    cT
    cmgmhm
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
    csubmgm
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
    mgmhmf
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
    mgmhmf
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
    cF
    cfv
    #
    @21
    cG
    cfv
    #
    wceq
    #
    @26
    wi
    #
    vx
    @9
    wral
    @27
    @3
    @31
    vx
    @9
    @3
    @21
    @9
    wcel
    #
    @30
    @26
    @3
    @32
    @30
    wa
    #
    wa
    #
    @22
    cF
    cfv
    #
    @22
    cG
    cfv
    #
    wceq
    #
    @25
    wi
    #
    vy
    @9
    wral
    @26
    @34
    @38
    vy
    @9
    @34
    @22
    @9
    wcel
    #
    @37
    @25
    @34
    @39
    @37
    wa
    #
    wa
    #
    @24
    @9
    wcel
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
    @25
    @41
    cS
    cmgm
    wcel
    #
    @32
    @39
    @42
    @3
    @46
    @33
    @40
    @1
    @46
    @2
    @1
    @46
    cT
    cmgm
    wcel
    cS
    cT
    cF
    mgmhmrcl
    simpld
    adantr
    #
    ad2antrr
    @3
    @32
    @30
    @40
    simplrl
    #
    @34
    @39
    @37
    simprl
    #
    @9
    cS
    @21
    @22
    @23
    @16
    @23
    eqid
    #
    mgmcl
    syl3anc
    @41
    @28
    @35
    cT
    cplusg
    cfv
    #
    co
    #
    @29
    @36
    @51
    co
    #
    @43
    @44
    @41
    @28
    @29
    @35
    @36
    @51
    @3
    @32
    @30
    @40
    simplrr
    @34
    @39
    @37
    simprr
    oveq12d
    @41
    @1
    @32
    @39
    @43
    @52
    wceq
    @1
    @2
    @33
    @40
    simplll
    @48
    @49
    @9
    @23
    @51
    cS
    cT
    cF
    @21
    @22
    @16
    @50
    @51
    eqid
    #
    mgmhmlin
    syl3anc
    @41
    @2
    @32
    @39
    @44
    @53
    wceq
    @1
    @2
    @33
    @40
    simpllr
    @48
    @49
    @9
    @23
    @51
    cS
    cT
    cG
    @21
    @22
    @16
    @50
    @54
    mgmhmlin
    syl3anc
    3eqtr4d
    @8
    @45
    vz
    @24
    @9
    @5
    @24
    wceq
    @6
    @43
    @7
    @44
    @5
    @24
    cF
    fveq2
    @5
    @24
    cG
    fveq2
    eqeq12d
    elrab
    sylanbrc
    expr
    ralrimiva
    @8
    @37
    @25
    vy
    vz
    @9
    @5
    @22
    wceq
    @6
    @35
    @7
    @36
    @5
    @22
    cF
    fveq2
    @5
    @22
    cG
    fveq2
    eqeq12d
    ralrab
    sylibr
    expr
    ralrimiva
    @8
    @30
    @26
    vx
    vz
    @9
    @5
    @21
    wceq
    @6
    @28
    @7
    @29
    @5
    @21
    cF
    fveq2
    @5
    @21
    cG
    fveq2
    eqeq12d
    ralrab
    sylibr
    @3
    @46
    @19
    @20
    @27
    wa
    wb
    @47
    vx
    vy
    @9
    @23
    @10
    cS
    @16
    @50
    issubmgm
    syl
    mpbir2and
    eqeltrd
end
