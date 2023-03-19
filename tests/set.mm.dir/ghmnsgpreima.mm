include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "cnsg.mm"
include "cfv.mm"
include "wa.mm"
include "ccnv.mm"
include "cima.mm"
include "csubg.mm"
include "cv.mm"
include "cplusg.mm"
include "csg.mm"
include "wral.mm"
include "cbs.mm"
include "nsgsubg.mm"
include "ghmpreima.mm"
include "sylan2.mm"
include "cgrp.mm"
include "ghmgrp1.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "simprr.mm"
include "wfn.mm"
include "wb.mm"
include "wf.mm"
include "simpll.mm"
include "eqid.mm"
include "ghmf.mm"
include "syl.mm"
include "ffn.mm"
include "elpreima.mm"
include "mpbid.mm"
include "simpld.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "grpsubcl.mm"
include "wceq.mm"
include "ghmsub.mm"
include "ghmlin.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "simplr.mm"
include "ffvelrnd.mm"
include "simprd.mm"
include "nsgconj.mm"
include "eqeltrd.mm"
include "mpbir2and.mm"
include "ralrimivva.mm"
include "isnsg3.mm"
include "sylanbrc.mm"

theorem ghmnsgpreima
  let cS: class S
  let cT: class T
  let cF: class F
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F e. ( S GrpHom T ) /\ V e. ( NrmSGrp ` T ) ) -> ( `' F " V ) e. ( NrmSGrp ` S ) )

  proof
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cV
    cT
    cnsg
    cfv
    wcel
    #
    wa
    #
    cF
    ccnv
    cV
    cima
    #
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
    cplusg
    cfv
    #
    co
    #
    @5
    cS
    csg
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
    vx
    cS
    cbs
    cfv
    #
    wral
    @3
    cS
    cnsg
    cfv
    wcel
    @1
    @0
    cV
    cT
    csubg
    cfv
    wcel
    @4
    cV
    cT
    nsgsubg
    cS
    cT
    cF
    cV
    ghmpreima
    sylan2
    @2
    @11
    vx
    vy
    @12
    @3
    @2
    @5
    @12
    wcel
    #
    @6
    @3
    wcel
    #
    wa
    #
    wa
    #
    @11
    @10
    @12
    wcel
    #
    @10
    cF
    cfv
    #
    cV
    wcel
    #
    @16
    cS
    cgrp
    wcel
    #
    @8
    @12
    wcel
    #
    @13
    @17
    @0
    @20
    @1
    @15
    cS
    cT
    cF
    ghmgrp1
    ad2antrr
    #
    @16
    @20
    @13
    @6
    @12
    wcel
    #
    @21
    @22
    @2
    @13
    @14
    simprl
    #
    @16
    @23
    @6
    cF
    cfv
    #
    cV
    wcel
    #
    @16
    @14
    @23
    @26
    wa
    #
    @2
    @13
    @14
    simprr
    @16
    cF
    @12
    wfn
    #
    @14
    @27
    wb
    @16
    @12
    cT
    cbs
    cfv
    #
    cF
    wf
    #
    @28
    @16
    @0
    @30
    @0
    @1
    @15
    simpll
    #
    cS
    cT
    cF
    @12
    @29
    @12
    eqid
    #
    @29
    eqid
    #
    ghmf
    syl
    #
    @12
    @29
    cF
    ffn
    syl
    #
    @12
    @6
    cV
    cF
    elpreima
    syl
    mpbid
    #
    simpld
    #
    @12
    @7
    cS
    @5
    @6
    @32
    @7
    eqid
    #
    grpcl
    syl3anc
    #
    @24
    @12
    cS
    @9
    @8
    @5
    @32
    @9
    eqid
    #
    grpsubcl
    syl3anc
    @16
    @18
    @5
    cF
    cfv
    #
    @25
    cT
    cplusg
    cfv
    #
    co
    #
    @41
    cT
    csg
    cfv
    #
    co
    #
    cV
    @16
    @18
    @8
    cF
    cfv
    #
    @41
    @44
    co
    #
    @45
    @16
    @0
    @21
    @13
    @18
    @47
    wceq
    @31
    @39
    @24
    @12
    cS
    cT
    @8
    cF
    @9
    @44
    @5
    @32
    @40
    @44
    eqid
    #
    ghmsub
    syl3anc
    @16
    @46
    @43
    @41
    @44
    @16
    @0
    @13
    @23
    @46
    @43
    wceq
    @31
    @24
    @37
    @7
    @42
    cS
    cT
    @5
    cF
    @6
    @12
    @32
    @38
    @42
    eqid
    #
    ghmlin
    syl3anc
    oveq1d
    eqtrd
    @16
    @1
    @41
    @29
    wcel
    @26
    @45
    cV
    wcel
    @0
    @1
    @15
    simplr
    @16
    @12
    @29
    @5
    cF
    @34
    @24
    ffvelrnd
    @16
    @23
    @26
    @36
    simprd
    @41
    @25
    @42
    cV
    cT
    @44
    @29
    @33
    @49
    @48
    nsgconj
    syl3anc
    eqeltrd
    @16
    @28
    @11
    @17
    @19
    wa
    wb
    @35
    @12
    @10
    cV
    cF
    elpreima
    syl
    mpbir2and
    ralrimivva
    vx
    vy
    @7
    @3
    cS
    @9
    @12
    @32
    @38
    @40
    isnsg3
    sylanbrc
end
