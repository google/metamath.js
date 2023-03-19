include "ctlm.mm"
include "wcel.mm"
include "cgrp.mm"
include "ctmd.mm"
include "cminusg.mm"
include "cfv.mm"
include "ctopn.mm"
include "ccn.mm"
include "co.mm"
include "ctgp.mm"
include "clmod.mm"
include "tlmlmod.mm"
include "lmodgrp.mm"
include "syl.mm"
include "tlmtmd.mm"
include "cbs.mm"
include "csca.mm"
include "cur.mm"
include "cv.mm"
include "cvsca.mm"
include "cmpt.mm"
include "wf.mm"
include "eqid.mm"
include "grpinvf.mm"
include "feqmptd.mm"
include "wceq.mm"
include "lmodvneg1.mm"
include "sylan.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "id.mm"
include "ctps.mm"
include "ctopon.mm"
include "tlmtps.mm"
include "istps.mm"
include "sylib.mm"
include "tlmscatps.mm"
include "crg.mm"
include "lmodring.mm"
include "ringgrp.mm"
include "ringidcl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "cnmptc.mm"
include "cnmptid.mm"
include "cnmpt1vsca.mm"
include "eqeltrd.mm"
include "istgp.mm"
include "syl3anbrc.mm"

theorem tlmtgp
  let cW: class W
  let vx: setvar x


  assert |- ( W e. TopMod -> W e. TopGrp )

  proof
    cW
    ctlm
    wcel
    #
    cW
    cgrp
    wcel
    #
    cW
    ctmd
    wcel
    cW
    cminusg
    cfv
    #
    cW
    ctopn
    cfv
    #
    @3
    ccn
    co
    #
    wcel
    cW
    ctgp
    wcel
    @0
    cW
    clmod
    wcel
    #
    @1
    cW
    tlmlmod
    #
    cW
    lmodgrp
    syl
    #
    cW
    tlmtmd
    @0
    @2
    vx
    cW
    cbs
    cfv
    #
    cW
    csca
    cfv
    #
    cur
    cfv
    #
    @9
    cminusg
    cfv
    #
    cfv
    #
    vx
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    @4
    @0
    @2
    vx
    @8
    @13
    @2
    cfv
    #
    cmpt
    @16
    @0
    vx
    @8
    @8
    @2
    @0
    @1
    @8
    @8
    @2
    wf
    @7
    @8
    cW
    @2
    @8
    eqid
    #
    @2
    eqid
    #
    grpinvf
    syl
    feqmptd
    @0
    vx
    @8
    @15
    @17
    @0
    @5
    @13
    @8
    wcel
    @15
    @17
    wceq
    @6
    @14
    @10
    @9
    @11
    @2
    @8
    cW
    @13
    @18
    @19
    @9
    eqid
    #
    @14
    eqid
    #
    @10
    eqid
    #
    @11
    eqid
    #
    lmodvneg1
    sylan
    mpteq2dva
    eqtr4d
    @0
    vx
    @12
    @13
    @14
    @9
    @3
    @9
    ctopn
    cfv
    #
    @3
    cW
    @8
    @20
    @21
    @3
    eqid
    #
    @24
    eqid
    #
    @0
    id
    @0
    cW
    ctps
    wcel
    @3
    @8
    ctopon
    cfv
    wcel
    cW
    tlmtps
    @8
    @3
    cW
    @18
    @25
    istps
    sylib
    #
    @0
    vx
    @12
    @3
    @24
    @8
    @9
    cbs
    cfv
    #
    @27
    @0
    @9
    ctps
    wcel
    @24
    @28
    ctopon
    cfv
    wcel
    @9
    cW
    @20
    tlmscatps
    @28
    @24
    @9
    @28
    eqid
    #
    @26
    istps
    sylib
    @0
    @9
    cgrp
    wcel
    #
    @10
    @28
    wcel
    #
    @12
    @28
    wcel
    @0
    @9
    crg
    wcel
    #
    @30
    @0
    @5
    @32
    @6
    @9
    cW
    @20
    lmodring
    syl
    #
    @9
    ringgrp
    syl
    @0
    @32
    @31
    @33
    @28
    @9
    @10
    @29
    @22
    ringidcl
    syl
    @28
    @9
    @11
    @10
    @29
    @23
    grpinvcl
    syl2anc
    cnmptc
    @0
    vx
    @3
    @8
    @27
    cnmptid
    cnmpt1vsca
    eqeltrd
    cW
    @2
    @3
    @25
    @19
    istgp
    syl3anbrc
end
