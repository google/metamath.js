include "clmod.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "csubg.mm"
include "cfv.mm"
include "cv.mm"
include "cvsca.mm"
include "wral.mm"
include "csca.mm"
include "cbs.mm"
include "cabl.mm"
include "lmodabl.mm"
include "3ad2ant1.mm"
include "lsssubg.mm"
include "3adant3.mm"
include "3adant2.mm"
include "lsmsubg2.mm"
include "syl3anc.mm"
include "wa.mm"
include "cplusg.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "eqid.mm"
include "lsmelval.mm"
include "syl2anc.mm"
include "adantr.mm"
include "simpll1.mm"
include "simplr.mm"
include "simpll2.mm"
include "simprl.mm"
include "lssel.mm"
include "simpll3.mm"
include "simprr.mm"
include "lmodvsdi.mm"
include "syl13anc.mm"
include "lssvscl.mm"
include "syl22anc.mm"
include "lsmelvali.mm"
include "eqeltrd.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "sylbid.mm"
include "impr.mm"
include "ralrimivva.mm"
include "islss4.mm"
include "mpbir2and.mm"

theorem lsmcl
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cU: class U
  let cW: class W
  let va: setvar a
  let vd: setvar d
  let ve: setvar e
  let vu: setvar u
  assume lsmcl.s: |- S = ( LSubSp ` W )
  assume lsmcl.p: |- .(+) = ( LSSum ` W )


  assert |- ( ( W e. LMod /\ T e. S /\ U e. S ) -> ( T .(+) U ) e. S )

  proof
    cW
    clmod
    wcel
    #
    cT
    cS
    wcel
    #
    cU
    cS
    wcel
    #
    w3a
    #
    cT
    cU
    c.po
    co
    #
    cS
    wcel
    #
    @4
    cW
    csubg
    cfv
    #
    wcel
    #
    va
    cv
    #
    vu
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    @4
    wcel
    #
    vu
    @4
    wral
    va
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    wral
    #
    @3
    cW
    cabl
    wcel
    #
    cT
    @6
    wcel
    #
    cU
    @6
    wcel
    #
    @7
    @0
    @1
    @16
    @2
    cW
    lmodabl
    3ad2ant1
    @0
    @1
    @17
    @2
    cS
    cT
    cW
    lsmcl.s
    lsssubg
    #
    3adant3
    #
    @0
    @2
    @18
    @1
    cS
    cU
    cW
    lsmcl.s
    lsssubg
    #
    3adant2
    #
    c.po
    cT
    cU
    cW
    lsmcl.p
    lsmsubg2
    syl3anc
    @3
    @12
    va
    vu
    @14
    @4
    @3
    @8
    @14
    wcel
    #
    @9
    @4
    wcel
    #
    @12
    @3
    @23
    wa
    #
    @24
    @9
    vd
    cv
    #
    ve
    cv
    #
    cW
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    ve
    cU
    wrex
    vd
    cT
    wrex
    #
    @12
    @3
    @24
    @31
    wb
    #
    @23
    @3
    @17
    @18
    @32
    @20
    @22
    vd
    ve
    @28
    c.po
    cT
    cU
    cW
    @9
    @28
    eqid
    #
    lsmcl.p
    lsmelval
    syl2anc
    adantr
    @25
    @30
    @12
    vd
    ve
    cT
    cU
    @25
    @26
    cT
    wcel
    #
    @27
    cU
    wcel
    #
    wa
    #
    wa
    #
    @12
    @30
    @8
    @29
    @10
    co
    #
    @4
    wcel
    @37
    @38
    @8
    @26
    @10
    co
    #
    @8
    @27
    @10
    co
    #
    @28
    co
    #
    @4
    @37
    @0
    @23
    @26
    cW
    cbs
    cfv
    #
    wcel
    #
    @27
    @42
    wcel
    #
    @38
    @41
    wceq
    @0
    @1
    @2
    @23
    @36
    simpll1
    #
    @3
    @23
    @36
    simplr
    #
    @37
    @1
    @34
    @43
    @0
    @1
    @2
    @23
    @36
    simpll2
    #
    @25
    @34
    @35
    simprl
    #
    cS
    cT
    @42
    cW
    @26
    @42
    eqid
    #
    lsmcl.s
    lssel
    syl2anc
    @37
    @2
    @35
    @44
    @0
    @1
    @2
    @23
    @36
    simpll3
    #
    @25
    @34
    @35
    simprr
    #
    cS
    cU
    @42
    cW
    @27
    @49
    lsmcl.s
    lssel
    syl2anc
    @28
    @8
    @10
    @13
    @14
    @42
    cW
    @26
    @27
    @49
    @33
    @13
    eqid
    #
    @10
    eqid
    #
    @14
    eqid
    #
    lmodvsdi
    syl13anc
    @37
    @17
    @18
    @39
    cT
    wcel
    #
    @40
    cU
    wcel
    #
    @41
    @4
    wcel
    @37
    @0
    @1
    @17
    @45
    @47
    @19
    syl2anc
    @37
    @0
    @2
    @18
    @45
    @50
    @21
    syl2anc
    @37
    @0
    @1
    @23
    @34
    @55
    @45
    @47
    @46
    @48
    @14
    cS
    @10
    cT
    @13
    cW
    @8
    @26
    @52
    @53
    @54
    lsmcl.s
    lssvscl
    syl22anc
    @37
    @0
    @2
    @23
    @35
    @56
    @45
    @50
    @46
    @51
    @14
    cS
    @10
    cU
    @13
    cW
    @8
    @27
    @52
    @53
    @54
    lsmcl.s
    lssvscl
    syl22anc
    @28
    c.po
    cT
    cU
    cW
    @39
    @40
    @33
    lsmcl.p
    lsmelvali
    syl22anc
    eqeltrd
    @30
    @11
    @38
    @4
    @9
    @29
    @8
    @10
    oveq2
    eleq1d
    syl5ibrcom
    rexlimdvva
    sylbid
    impr
    ralrimivva
    @0
    @1
    @5
    @7
    @15
    wa
    wb
    @2
    @14
    cS
    @10
    @4
    @13
    @42
    cW
    va
    vu
    @52
    @54
    @49
    @53
    lsmcl.s
    islss4
    3ad2ant1
    mpbir2and
end
