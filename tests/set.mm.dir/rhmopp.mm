include "crh.mm"
include "co.mm"
include "wcel.mm"
include "coppr.mm"
include "cfv.mm"
include "cbs.mm"
include "cmulr.mm"
include "cur.mm"
include "eqid.mm"
include "crg.mm"
include "rhmrcl1.mm"
include "opprringb.mm"
include "sylib.mm"
include "rhmrcl2.mm"
include "oppr1.mm"
include "eqcomi.mm"
include "rhm1.mm"
include "cv.mm"
include "wa.mm"
include "wceq.mm"
include "simpl.mm"
include "simprr.mm"
include "opprbas.mm"
include "syl6eleqr.mm"
include "simprl.mm"
include "rhmmul.mm"
include "syl3anc.mm"
include "opprmul.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"
include "cgrp.mm"
include "wf.mm"
include "cplusg.mm"
include "wral.mm"
include "cghm.mm"
include "ringgrp.mm"
include "syl.mm"
include "rhmf.mm"
include "rhmghm.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "ghmlin.mm"
include "ralrimiva.mm"
include "jca.mm"
include "jca31.mm"
include "oppradd.mm"
include "isghm.mm"
include "sylibr.mm"
include "isrhm2d.mm"

theorem rhmopp
  let cR: class R
  let cS: class S
  let cF: class F
  let vx: setvar x
  let vy: setvar y


  assert |- ( F e. ( R RingHom S ) -> F e. ( ( oppR ` R ) RingHom ( oppR ` S ) ) )

  proof
    cF
    cR
    cS
    crh
    co
    wcel
    #
    vx
    vy
    cR
    coppr
    cfv
    #
    cbs
    cfv
    #
    @1
    cS
    coppr
    cfv
    #
    @1
    cmulr
    cfv
    #
    @3
    cmulr
    cfv
    #
    @1
    cur
    cfv
    #
    cF
    @3
    cur
    cfv
    #
    @2
    eqid
    @6
    eqid
    @7
    eqid
    @4
    eqid
    #
    @5
    eqid
    #
    @0
    cR
    crg
    wcel
    @1
    crg
    wcel
    #
    cR
    cS
    cF
    rhmrcl1
    cR
    @1
    @1
    eqid
    #
    opprringb
    sylib
    #
    @0
    cS
    crg
    wcel
    @3
    crg
    wcel
    #
    cR
    cS
    cF
    rhmrcl2
    cS
    @3
    @3
    eqid
    #
    opprringb
    sylib
    #
    cR
    cS
    @6
    cF
    @7
    cR
    cur
    cfv
    #
    @6
    cR
    @16
    @1
    @11
    @16
    eqid
    oppr1
    eqcomi
    cS
    cur
    cfv
    #
    @7
    cS
    @17
    @3
    @14
    @17
    eqid
    oppr1
    eqcomi
    rhm1
    @0
    vx
    cv
    #
    @2
    wcel
    #
    vy
    cv
    #
    @2
    wcel
    #
    wa
    #
    wa
    #
    @20
    @18
    cR
    cmulr
    cfv
    #
    co
    #
    cF
    cfv
    #
    @20
    cF
    cfv
    #
    @18
    cF
    cfv
    #
    cS
    cmulr
    cfv
    #
    co
    #
    @18
    @20
    @4
    co
    #
    cF
    cfv
    @28
    @27
    @5
    co
    @23
    @0
    @20
    cR
    cbs
    cfv
    #
    wcel
    #
    @18
    @32
    wcel
    #
    @26
    @30
    wceq
    @0
    @22
    simpl
    @23
    @20
    @2
    @32
    @0
    @19
    @21
    simprr
    @32
    cR
    @1
    @11
    @32
    eqid
    #
    opprbas
    #
    syl6eleqr
    @23
    @18
    @2
    @32
    @0
    @19
    @21
    simprl
    @36
    syl6eleqr
    @20
    @18
    cR
    cS
    @24
    @29
    cF
    @32
    @35
    @24
    eqid
    #
    @29
    eqid
    #
    rhmmul
    syl3anc
    @31
    @25
    cF
    @32
    cR
    @4
    @24
    @1
    @18
    @20
    @35
    @37
    @11
    @8
    opprmul
    fveq2i
    cS
    cbs
    cfv
    #
    cS
    @5
    @29
    @3
    @28
    @27
    @39
    eqid
    #
    @38
    @14
    @9
    opprmul
    3eqtr4g
    @0
    @1
    cgrp
    wcel
    #
    @3
    cgrp
    wcel
    #
    wa
    @32
    @39
    cF
    wf
    #
    @18
    @20
    cR
    cplusg
    cfv
    #
    co
    cF
    cfv
    @28
    @27
    cS
    cplusg
    cfv
    #
    co
    wceq
    #
    vy
    @32
    wral
    #
    vx
    @32
    wral
    #
    wa
    #
    wa
    cF
    @1
    @3
    cghm
    co
    wcel
    @0
    @41
    @42
    @49
    @0
    @10
    @41
    @12
    @1
    ringgrp
    syl
    @0
    @13
    @42
    @15
    @3
    ringgrp
    syl
    @0
    @43
    @48
    @32
    @39
    cR
    cS
    cF
    @35
    @40
    rhmf
    @0
    @47
    vx
    @32
    @0
    @34
    wa
    #
    @46
    vy
    @32
    @50
    @33
    wa
    cF
    cR
    cS
    cghm
    co
    wcel
    #
    @34
    @33
    @46
    @0
    @51
    @34
    @33
    cR
    cS
    cF
    rhmghm
    ad2antrr
    @0
    @34
    @33
    simplr
    @50
    @33
    simpr
    @44
    @45
    cR
    cS
    @18
    cF
    @20
    @32
    @35
    @44
    eqid
    #
    @45
    eqid
    #
    ghmlin
    syl3anc
    ralrimiva
    ralrimiva
    jca
    jca31
    vy
    vx
    @44
    @45
    @1
    @3
    cF
    @32
    @39
    @36
    @39
    cS
    @3
    @14
    @40
    opprbas
    @44
    cR
    @1
    @11
    @52
    oppradd
    @45
    cS
    @3
    @14
    @53
    oppradd
    isghm
    sylibr
    isrhm2d
end
