include "cabl.mm"
include "wcel.mm"
include "cgim.mm"
include "co.mm"
include "wa.mm"
include "cgrp.mm"
include "ccmn.mm"
include "cghm.mm"
include "gimghm.mm"
include "ghmgrp2.mm"
include "syl.mm"
include "adantl.mm"
include "cmnd.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "grpmnd.mm"
include "ccnv.mm"
include "simpll.mm"
include "wf.mm"
include "wf1o.mm"
include "eqid.mm"
include "gimf1o.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "simprr.mm"
include "ablcom.mm"
include "syl3anc.mm"
include "gimcnv.mm"
include "ghmlin.mm"
include "3eqtr4d.mm"
include "fveq2d.mm"
include "grpcl.mm"
include "f1ocnvfv2.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "ralrimivva.mm"
include "iscmn.mm"
include "sylanbrc.mm"
include "isabl.mm"

theorem abliso
  let cF: class F
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( M e. Abel /\ F e. ( M GrpIso N ) ) -> N e. Abel )

  proof
    cM
    cabl
    wcel
    #
    cF
    cM
    cN
    cgim
    co
    wcel
    #
    wa
    #
    cN
    cgrp
    wcel
    #
    cN
    ccmn
    wcel
    #
    cN
    cabl
    wcel
    @1
    @3
    @0
    @1
    cF
    cM
    cN
    cghm
    co
    wcel
    @3
    cM
    cN
    cF
    gimghm
    cM
    cN
    cF
    ghmgrp2
    syl
    #
    adantl
    #
    @2
    cN
    cmnd
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
    @9
    @8
    @10
    co
    #
    wceq
    #
    vy
    cN
    cbs
    cfv
    #
    wral
    vx
    @14
    wral
    @4
    @2
    @3
    @7
    @6
    cN
    grpmnd
    syl
    @2
    @13
    vx
    vy
    @14
    @14
    @2
    @8
    @14
    wcel
    #
    @9
    @14
    wcel
    #
    wa
    #
    wa
    #
    @11
    cF
    ccnv
    #
    cfv
    #
    cF
    cfv
    #
    @12
    @19
    cfv
    #
    cF
    cfv
    #
    @11
    @12
    @18
    @20
    @22
    cF
    @18
    @8
    @19
    cfv
    #
    @9
    @19
    cfv
    #
    cM
    cplusg
    cfv
    #
    co
    #
    @25
    @24
    @26
    co
    #
    @20
    @22
    @18
    @0
    @24
    cM
    cbs
    cfv
    #
    wcel
    @25
    @29
    wcel
    @27
    @28
    wceq
    @0
    @1
    @17
    simpll
    @18
    @14
    @29
    @8
    @19
    @1
    @14
    @29
    @19
    wf
    #
    @0
    @17
    @1
    @29
    @14
    cF
    wf1o
    #
    @14
    @29
    @19
    wf1o
    @30
    @29
    @14
    cM
    cN
    cF
    @29
    eqid
    #
    @14
    eqid
    #
    gimf1o
    #
    @29
    @14
    cF
    f1ocnv
    @14
    @29
    @19
    f1of
    3syl
    ad2antlr
    #
    @2
    @15
    @16
    simprl
    #
    ffvelrnd
    @18
    @14
    @29
    @9
    @19
    @35
    @2
    @15
    @16
    simprr
    #
    ffvelrnd
    @29
    @26
    cM
    @24
    @25
    @32
    @26
    eqid
    #
    ablcom
    syl3anc
    @18
    @19
    cN
    cM
    cghm
    co
    wcel
    #
    @15
    @16
    @20
    @27
    wceq
    @18
    @19
    cN
    cM
    cgim
    co
    wcel
    #
    @39
    @1
    @40
    @0
    @17
    cM
    cN
    cF
    gimcnv
    ad2antlr
    cN
    cM
    @19
    gimghm
    syl
    #
    @36
    @37
    @10
    @26
    cN
    cM
    @8
    @19
    @9
    @14
    @33
    @10
    eqid
    #
    @38
    ghmlin
    syl3anc
    @18
    @39
    @16
    @15
    @22
    @28
    wceq
    @41
    @37
    @36
    @10
    @26
    cN
    cM
    @9
    @19
    @8
    @14
    @33
    @42
    @38
    ghmlin
    syl3anc
    3eqtr4d
    fveq2d
    @18
    @31
    @11
    @14
    wcel
    #
    @21
    @11
    wceq
    @1
    @31
    @0
    @17
    @34
    ad2antlr
    #
    @18
    @3
    @15
    @16
    @43
    @1
    @3
    @0
    @17
    @5
    ad2antlr
    #
    @36
    @37
    @14
    @10
    cN
    @8
    @9
    @33
    @42
    grpcl
    syl3anc
    @29
    @14
    @11
    cF
    f1ocnvfv2
    syl2anc
    @18
    @31
    @12
    @14
    wcel
    #
    @23
    @12
    wceq
    @44
    @18
    @3
    @16
    @15
    @46
    @45
    @37
    @36
    @14
    @10
    cN
    @9
    @8
    @33
    @42
    grpcl
    syl3anc
    @29
    @14
    @12
    cF
    f1ocnvfv2
    syl2anc
    3eqtr3d
    ralrimivva
    vx
    vy
    @14
    @10
    cN
    @33
    @42
    iscmn
    sylanbrc
    cN
    isabl
    sylanbrc
end
