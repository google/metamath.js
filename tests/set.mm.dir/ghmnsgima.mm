include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "cnsg.mm"
include "cfv.mm"
include "crn.mm"
include "wceq.mm"
include "w3a.mm"
include "cima.mm"
include "csubg.mm"
include "cv.mm"
include "cplusg.mm"
include "csg.mm"
include "wral.mm"
include "simp1.mm"
include "nsgsubg.mm"
include "3ad2ant2.mm"
include "ghmima.mm"
include "syl2anc.mm"
include "cbs.mm"
include "wa.mm"
include "adantr.mm"
include "cgrp.mm"
include "ghmgrp1.mm"
include "syl.mm"
include "simprl.mm"
include "wss.mm"
include "eqid.mm"
include "subgss.mm"
include "simprr.mm"
include "sseldd.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "ghmsub.mm"
include "ghmlin.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "wfn.mm"
include "wf.mm"
include "ghmf.mm"
include "ffn.mm"
include "simpl2.mm"
include "nsgconj.mm"
include "fnfvima.mm"
include "eqeltrrd.mm"
include "ralrimivva.mm"
include "wb.mm"
include "oveq1.mm"
include "id.mm"
include "oveq12d.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "ralrn.mm"
include "simp3.mm"
include "raleqdv.mm"
include "oveq2.mm"
include "ralima.mm"
include "3bitr3d.mm"
include "mpbird.mm"
include "isnsg3.mm"
include "sylanbrc.mm"

theorem ghmnsgima
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ghmnsgima.1: |- Y = ( Base ` T )


  assert |- ( ( F e. ( S GrpHom T ) /\ U e. ( NrmSGrp ` S ) /\ ran F = Y ) -> ( F " U ) e. ( NrmSGrp ` T ) )

  proof
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cU
    cS
    cnsg
    cfv
    wcel
    #
    cF
    crn
    #
    cY
    wceq
    #
    w3a
    #
    cF
    cU
    cima
    #
    cT
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
    cT
    cplusg
    cfv
    #
    co
    #
    @7
    cT
    csg
    cfv
    #
    co
    #
    @5
    wcel
    #
    vy
    @5
    wral
    #
    vx
    cY
    wral
    #
    @5
    cT
    cnsg
    cfv
    wcel
    @4
    @0
    cU
    cS
    csubg
    cfv
    wcel
    #
    @6
    @0
    @1
    @3
    simp1
    #
    @1
    @0
    @16
    @3
    cU
    cS
    nsgsubg
    3ad2ant2
    #
    cS
    cT
    cU
    cF
    ghmima
    syl2anc
    @4
    @15
    vz
    cv
    #
    cF
    cfv
    #
    @7
    cF
    cfv
    #
    @9
    co
    #
    @20
    @11
    co
    #
    @5
    wcel
    #
    vx
    cU
    wral
    #
    vz
    cS
    cbs
    cfv
    #
    wral
    #
    @4
    @24
    vz
    vx
    @26
    cU
    @4
    @19
    @26
    wcel
    #
    @7
    cU
    wcel
    #
    wa
    #
    wa
    #
    @19
    @7
    cS
    cplusg
    cfv
    #
    co
    #
    @19
    cS
    csg
    cfv
    #
    co
    #
    cF
    cfv
    #
    @23
    @5
    @31
    @36
    @33
    cF
    cfv
    #
    @20
    @11
    co
    #
    @23
    @31
    @0
    @33
    @26
    wcel
    #
    @28
    @36
    @38
    wceq
    @4
    @0
    @30
    @17
    adantr
    #
    @31
    cS
    cgrp
    wcel
    #
    @28
    @7
    @26
    wcel
    #
    @39
    @31
    @0
    @41
    @40
    cS
    cT
    cF
    ghmgrp1
    syl
    @4
    @28
    @29
    simprl
    #
    @31
    cU
    @26
    @7
    @4
    cU
    @26
    wss
    #
    @30
    @4
    @16
    @44
    @18
    @26
    cU
    cS
    @26
    eqid
    #
    subgss
    syl
    #
    adantr
    #
    @4
    @28
    @29
    simprr
    #
    sseldd
    #
    @26
    @32
    cS
    @19
    @7
    @45
    @32
    eqid
    #
    grpcl
    syl3anc
    @43
    @26
    cS
    cT
    @33
    cF
    @34
    @11
    @19
    @45
    @34
    eqid
    #
    @11
    eqid
    #
    ghmsub
    syl3anc
    @31
    @37
    @22
    @20
    @11
    @31
    @0
    @28
    @42
    @37
    @22
    wceq
    @40
    @43
    @49
    @32
    @9
    cS
    cT
    @19
    cF
    @7
    @26
    @45
    @50
    @9
    eqid
    #
    ghmlin
    syl3anc
    oveq1d
    eqtrd
    @31
    cF
    @26
    wfn
    #
    @44
    @35
    cU
    wcel
    #
    @36
    @5
    wcel
    @31
    @26
    cY
    cF
    wf
    #
    @54
    @4
    @56
    @30
    @4
    @0
    @56
    @17
    cS
    cT
    cF
    @26
    cY
    @45
    ghmnsgima.1
    ghmf
    syl
    #
    adantr
    @26
    cY
    cF
    ffn
    #
    syl
    @47
    @31
    @1
    @28
    @29
    @55
    @0
    @1
    @3
    @30
    simpl2
    @43
    @48
    @19
    @7
    @32
    cU
    cS
    @34
    @26
    @45
    @50
    @51
    nsgconj
    syl3anc
    @26
    cU
    cF
    @35
    fnfvima
    syl3anc
    eqeltrrd
    ralrimivva
    @4
    @14
    vx
    @2
    wral
    #
    @20
    @8
    @9
    co
    #
    @20
    @11
    co
    #
    @5
    wcel
    #
    vy
    @5
    wral
    #
    vz
    @26
    wral
    #
    @15
    @27
    @4
    @54
    @59
    @64
    wb
    @4
    @56
    @54
    @57
    @58
    syl
    #
    @14
    @63
    vx
    vz
    @26
    cF
    @7
    @20
    wceq
    #
    @13
    @62
    vy
    @5
    @66
    @12
    @61
    @5
    @66
    @10
    @60
    @7
    @20
    @11
    @7
    @20
    @8
    @9
    oveq1
    @66
    id
    oveq12d
    eleq1d
    ralbidv
    ralrn
    syl
    @4
    @14
    vx
    @2
    cY
    @0
    @1
    @3
    simp3
    raleqdv
    @4
    @63
    @25
    vz
    @26
    @4
    @54
    @44
    @63
    @25
    wb
    @65
    @46
    @62
    @24
    vy
    vx
    @26
    cU
    cF
    @8
    @21
    wceq
    #
    @61
    @23
    @5
    @67
    @60
    @22
    @20
    @11
    @8
    @21
    @20
    @9
    oveq2
    oveq1d
    eleq1d
    ralima
    syl2anc
    ralbidv
    3bitr3d
    mpbird
    vx
    vy
    @9
    @5
    cT
    @11
    cY
    ghmnsgima.1
    @53
    @52
    isnsg3
    sylanbrc
end
