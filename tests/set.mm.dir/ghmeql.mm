include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cin.mm"
include "cdm.mm"
include "csubg.mm"
include "cfv.mm"
include "csubmnd.mm"
include "cv.mm"
include "cminusg.mm"
include "wral.mm"
include "cmhm.mm"
include "ghmmhm.mm"
include "mhmeql.mm"
include "syl2an.mm"
include "wceq.mm"
include "cbs.mm"
include "crab.mm"
include "wi.mm"
include "cgrp.mm"
include "ghmgrp1.mm"
include "adantr.mm"
include "simprl.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "simprr.mm"
include "fveq2d.mm"
include "ghminv.mm"
include "ad2ant2r.mm"
include "ad2ant2lr.mm"
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
include "wfn.mm"
include "wf.mm"
include "ghmf.mm"
include "ffn.mm"
include "syl.mm"
include "adantl.mm"
include "fndmin.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "mpbird.mm"
include "issubg3.mm"
include "mpbir2and.mm"

theorem ghmeql
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F e. ( S GrpHom T ) /\ G e. ( S GrpHom T ) ) -> dom ( F i^i G ) e. ( SubGrp ` S ) )

  proof
    cF
    cS
    cT
    cghm
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
    cS
    csubg
    cfv
    wcel
    #
    @4
    cS
    csubmnd
    cfv
    wcel
    #
    vx
    cv
    #
    cS
    cminusg
    cfv
    #
    cfv
    #
    @4
    wcel
    #
    vx
    @4
    wral
    #
    @1
    cF
    cS
    cT
    cmhm
    co
    #
    wcel
    cG
    @12
    wcel
    @6
    @2
    cS
    cT
    cF
    ghmmhm
    cS
    cT
    cG
    ghmmhm
    cS
    cT
    cF
    cG
    mhmeql
    syl2an
    @3
    @11
    @9
    vy
    cv
    #
    cF
    cfv
    #
    @13
    cG
    cfv
    #
    wceq
    #
    vy
    cS
    cbs
    cfv
    #
    crab
    #
    wcel
    #
    vx
    @18
    wral
    #
    @3
    @7
    cF
    cfv
    #
    @7
    cG
    cfv
    #
    wceq
    #
    @19
    wi
    #
    vx
    @17
    wral
    @20
    @3
    @24
    vx
    @17
    @3
    @7
    @17
    wcel
    #
    @23
    @19
    @3
    @25
    @23
    wa
    #
    wa
    #
    @9
    @17
    wcel
    #
    @9
    cF
    cfv
    #
    @9
    cG
    cfv
    #
    wceq
    #
    @19
    @27
    cS
    cgrp
    wcel
    #
    @25
    @28
    @3
    @32
    @26
    @1
    @32
    @2
    cS
    cT
    cF
    ghmgrp1
    adantr
    #
    adantr
    @3
    @25
    @23
    simprl
    @17
    cS
    @8
    @7
    @17
    eqid
    #
    @8
    eqid
    #
    grpinvcl
    syl2anc
    @27
    @21
    cT
    cminusg
    cfv
    #
    cfv
    #
    @22
    @36
    cfv
    #
    @29
    @30
    @27
    @21
    @22
    @36
    @3
    @25
    @23
    simprr
    fveq2d
    @1
    @25
    @29
    @37
    wceq
    @2
    @23
    @17
    cS
    cT
    cF
    @8
    @36
    @7
    @34
    @35
    @36
    eqid
    #
    ghminv
    ad2ant2r
    @2
    @25
    @30
    @38
    wceq
    @1
    @23
    @17
    cS
    cT
    cG
    @8
    @36
    @7
    @34
    @35
    @39
    ghminv
    ad2ant2lr
    3eqtr4d
    @16
    @31
    vy
    @9
    @17
    @13
    @9
    wceq
    @14
    @29
    @15
    @30
    @13
    @9
    cF
    fveq2
    @13
    @9
    cG
    fveq2
    eqeq12d
    elrab
    sylanbrc
    expr
    ralrimiva
    @16
    @23
    @19
    vx
    vy
    @17
    @13
    @7
    wceq
    @14
    @21
    @15
    @22
    @13
    @7
    cF
    fveq2
    @13
    @7
    cG
    fveq2
    eqeq12d
    ralrab
    sylibr
    @3
    @4
    @18
    wceq
    #
    @11
    @20
    wb
    @3
    cF
    @17
    wfn
    #
    cG
    @17
    wfn
    #
    @40
    @3
    @17
    cT
    cbs
    cfv
    #
    cF
    wf
    #
    @41
    @1
    @44
    @2
    cS
    cT
    cF
    @17
    @43
    @34
    @43
    eqid
    #
    ghmf
    adantr
    @17
    @43
    cF
    ffn
    syl
    @3
    @17
    @43
    cG
    wf
    #
    @42
    @2
    @46
    @1
    cS
    cT
    cG
    @17
    @43
    @34
    @45
    ghmf
    adantl
    @17
    @43
    cG
    ffn
    syl
    vy
    @17
    cF
    cG
    fndmin
    syl2anc
    @10
    @19
    vx
    @4
    @18
    @4
    @18
    @9
    eleq2
    raleqbi1dv
    syl
    mpbird
    @3
    @32
    @5
    @6
    @11
    wa
    wb
    @33
    vx
    @4
    cS
    @8
    @35
    issubg3
    syl
    mpbir2and
end
