include "clmod.mm"
include "wcel.mm"
include "ccmn.mm"
include "csca.mm"
include "cfv.mm"
include "csrg.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "cbs.mm"
include "cplusg.mm"
include "wceq.mm"
include "w3a.mm"
include "cmulr.mm"
include "cur.mm"
include "c0g.mm"
include "wa.mm"
include "wral.mm"
include "cslmd.mm"
include "lmodcmn.mm"
include "crg.mm"
include "eqid.mm"
include "lmodring.mm"
include "ringsrg.mm"
include "syl.mm"
include "cgrp.mm"
include "islmod.mm"
include "simp3bi.mm"
include "r19.21bi.mm"
include "simpld.mm"
include "simprd.mm"
include "simp-4l.mm"
include "lmod0vs.mm"
include "sylancom.mm"
include "3jca.mm"
include "jca.mm"
include "ralrimiva.mm"
include "isslmd.mm"
include "syl3anbrc.mm"

theorem lmodslmd
  let cW: class W
  let vq: setvar q
  let vr: setvar r
  let vw: setvar w
  let vx: setvar x


  assert |- ( W e. LMod -> W e. SLMod )

  proof
    cW
    clmod
    wcel
    #
    cW
    ccmn
    wcel
    cW
    csca
    cfv
    #
    csrg
    wcel
    #
    vr
    cv
    #
    vw
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    cW
    cbs
    cfv
    #
    wcel
    @3
    @4
    vx
    cv
    #
    cW
    cplusg
    cfv
    #
    co
    @5
    co
    @6
    @3
    @8
    @5
    co
    @9
    co
    wceq
    vq
    cv
    #
    @3
    @1
    cplusg
    cfv
    #
    co
    @4
    @5
    co
    @10
    @4
    @5
    co
    @6
    @9
    co
    wceq
    w3a
    #
    @10
    @3
    @1
    cmulr
    cfv
    #
    co
    @4
    @5
    co
    @10
    @6
    @5
    co
    wceq
    #
    @1
    cur
    cfv
    #
    @4
    @5
    co
    @4
    wceq
    #
    @1
    c0g
    cfv
    #
    @4
    @5
    co
    cW
    c0g
    cfv
    #
    wceq
    #
    w3a
    #
    wa
    #
    vw
    @7
    wral
    #
    vx
    @7
    wral
    #
    vr
    @1
    cbs
    cfv
    #
    wral
    #
    vq
    @24
    wral
    cW
    cslmd
    wcel
    cW
    lmodcmn
    @0
    @1
    crg
    wcel
    #
    @2
    @1
    cW
    @1
    eqid
    #
    lmodring
    @1
    ringsrg
    syl
    @0
    @25
    vq
    @24
    @0
    @10
    @24
    wcel
    #
    wa
    #
    @23
    vr
    @24
    @29
    @3
    @24
    wcel
    #
    wa
    #
    @22
    vx
    @7
    @31
    @8
    @7
    wcel
    #
    wa
    #
    @21
    vw
    @7
    @33
    @4
    @7
    wcel
    #
    wa
    #
    @12
    @20
    @35
    @12
    @14
    @16
    wa
    #
    @33
    @12
    @36
    wa
    #
    vw
    @7
    @31
    @37
    vw
    @7
    wral
    #
    vx
    @7
    @29
    @38
    vx
    @7
    wral
    #
    vr
    @24
    @0
    @39
    vr
    @24
    wral
    #
    vq
    @24
    @0
    cW
    cgrp
    wcel
    @26
    @40
    vq
    @24
    wral
    vx
    vw
    @9
    @11
    @5
    @13
    @15
    @1
    @24
    @7
    cW
    vr
    vq
    @7
    eqid
    #
    @9
    eqid
    #
    @5
    eqid
    #
    @27
    @24
    eqid
    #
    @11
    eqid
    #
    @13
    eqid
    #
    @15
    eqid
    #
    islmod
    simp3bi
    r19.21bi
    r19.21bi
    r19.21bi
    r19.21bi
    #
    simpld
    @35
    @14
    @16
    @19
    @35
    @14
    @16
    @35
    @12
    @36
    @48
    simprd
    #
    simpld
    @35
    @14
    @16
    @49
    simprd
    @33
    @34
    @0
    @19
    @0
    @28
    @30
    @32
    @34
    simp-4l
    @5
    @1
    @17
    @7
    cW
    @4
    @18
    @41
    @27
    @43
    @17
    eqid
    #
    @18
    eqid
    #
    lmod0vs
    sylancom
    3jca
    jca
    ralrimiva
    ralrimiva
    ralrimiva
    ralrimiva
    vx
    vw
    @9
    @11
    @5
    @13
    @15
    @1
    @24
    @17
    @7
    cW
    @18
    vr
    vq
    @41
    @42
    @43
    @51
    @27
    @44
    @45
    @46
    @47
    @50
    isslmd
    syl3anbrc
end
