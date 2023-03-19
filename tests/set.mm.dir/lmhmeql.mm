include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cin.mm"
include "cdm.mm"
include "csubg.mm"
include "cfv.mm"
include "cv.mm"
include "cvsca.mm"
include "wral.mm"
include "csca.mm"
include "cbs.mm"
include "cghm.mm"
include "lmghm.mm"
include "ghmeql.mm"
include "syl2an.mm"
include "wceq.mm"
include "crab.mm"
include "wi.mm"
include "clmod.mm"
include "lmhmlmod1.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simprl.mm"
include "eqid.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "oveq2.mm"
include "ad2antll.mm"
include "simplll.mm"
include "lmhmlin.mm"
include "simpllr.mm"
include "3eqtr4d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "expr.mm"
include "ralrimiva.mm"
include "wb.mm"
include "wfn.mm"
include "wf.mm"
include "lmhmf.mm"
include "ffn.mm"
include "syl.mm"
include "fndmin.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "ralrab.mm"
include "syl6bb.mm"
include "mpbird.mm"
include "islss4.mm"
include "mpbir2and.mm"

theorem lmhmeql
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lmhmeql.u: |- U = ( LSubSp ` S )


  assert |- ( ( F e. ( S LMHom T ) /\ G e. ( S LMHom T ) ) -> dom ( F i^i G ) e. U )

  proof
    cF
    cS
    cT
    clmhm
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
    cU
    wcel
    #
    @4
    cS
    csubg
    cfv
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cS
    cvsca
    cfv
    #
    co
    #
    @4
    wcel
    #
    vy
    @4
    wral
    #
    vx
    cS
    csca
    cfv
    #
    cbs
    cfv
    #
    wral
    #
    @1
    cF
    cS
    cT
    cghm
    co
    #
    wcel
    cG
    @16
    wcel
    @6
    @2
    cS
    cT
    cF
    lmghm
    cS
    cT
    cG
    lmghm
    cS
    cT
    cF
    cG
    ghmeql
    syl2an
    @3
    @12
    vx
    @14
    @3
    @7
    @14
    wcel
    #
    wa
    #
    @12
    @8
    cF
    cfv
    #
    @8
    cG
    cfv
    #
    wceq
    #
    @10
    vz
    cv
    #
    cF
    cfv
    #
    @22
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
    wcel
    #
    wi
    #
    vy
    @26
    wral
    #
    @18
    @29
    vy
    @26
    @18
    @8
    @26
    wcel
    #
    @21
    @28
    @18
    @31
    @21
    wa
    #
    wa
    #
    @10
    @26
    wcel
    #
    @10
    cF
    cfv
    #
    @10
    cG
    cfv
    #
    wceq
    #
    @28
    @33
    cS
    clmod
    wcel
    #
    @17
    @31
    @34
    @3
    @38
    @17
    @32
    @1
    @38
    @2
    cS
    cT
    cF
    lmhmlmod1
    adantr
    #
    ad2antrr
    @3
    @17
    @32
    simplr
    #
    @18
    @31
    @21
    simprl
    #
    @7
    @9
    @13
    @14
    @26
    cS
    @8
    @26
    eqid
    #
    @13
    eqid
    #
    @9
    eqid
    #
    @14
    eqid
    #
    lmodvscl
    syl3anc
    @33
    @7
    @19
    cT
    cvsca
    cfv
    #
    co
    #
    @7
    @20
    @46
    co
    #
    @35
    @36
    @21
    @47
    @48
    wceq
    @18
    @31
    @19
    @20
    @7
    @46
    oveq2
    ad2antll
    @33
    @1
    @17
    @31
    @35
    @47
    wceq
    @1
    @2
    @17
    @32
    simplll
    @40
    @41
    @14
    cS
    cT
    @9
    @46
    @26
    cF
    @13
    @7
    @8
    @43
    @45
    @42
    @44
    @46
    eqid
    #
    lmhmlin
    syl3anc
    @33
    @2
    @17
    @31
    @36
    @48
    wceq
    @1
    @2
    @17
    @32
    simpllr
    @40
    @41
    @14
    cS
    cT
    @9
    @46
    @26
    cG
    @13
    @7
    @8
    @43
    @45
    @42
    @44
    @49
    lmhmlin
    syl3anc
    3eqtr4d
    @25
    @37
    vz
    @10
    @26
    @22
    @10
    wceq
    @23
    @35
    @24
    @36
    @22
    @10
    cF
    fveq2
    @22
    @10
    cG
    fveq2
    eqeq12d
    elrab
    sylanbrc
    expr
    ralrimiva
    @18
    @4
    @27
    wceq
    #
    @12
    @30
    wb
    @3
    @50
    @17
    @1
    cF
    @26
    wfn
    #
    cG
    @26
    wfn
    #
    @50
    @2
    @1
    @26
    cT
    cbs
    cfv
    #
    cF
    wf
    @51
    @26
    @53
    cS
    cT
    cF
    @42
    @53
    eqid
    #
    lmhmf
    @26
    @53
    cF
    ffn
    syl
    @2
    @26
    @53
    cG
    wf
    @52
    @26
    @53
    cS
    cT
    cG
    @42
    @54
    lmhmf
    @26
    @53
    cG
    ffn
    syl
    vz
    @26
    cF
    cG
    fndmin
    syl2an
    adantr
    @50
    @12
    @28
    vy
    @27
    wral
    @30
    @11
    @28
    vy
    @4
    @27
    @4
    @27
    @10
    eleq2
    raleqbi1dv
    @25
    @21
    @28
    vy
    vz
    @26
    @22
    @8
    wceq
    @23
    @19
    @24
    @20
    @22
    @8
    cF
    fveq2
    @22
    @8
    cG
    fveq2
    eqeq12d
    ralrab
    syl6bb
    syl
    mpbird
    ralrimiva
    @3
    @38
    @5
    @6
    @15
    wa
    wb
    @39
    @14
    cU
    @9
    @4
    @13
    @26
    cS
    vx
    vy
    @43
    @45
    @42
    @44
    lmhmeql.u
    islss4
    syl
    mpbir2and
end
