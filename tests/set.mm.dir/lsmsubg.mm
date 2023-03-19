include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "co.mm"
include "csubmnd.mm"
include "cv.mm"
include "cminusg.mm"
include "wral.mm"
include "simp1.mm"
include "subgsubm.mm"
include "syl.mm"
include "simp2.mm"
include "simp3.mm"
include "lsmsubm.mm"
include "syl3anc.mm"
include "cplusg.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "eqid.mm"
include "lsmelval.mm"
include "3adant3.mm"
include "wa.mm"
include "cgrp.mm"
include "cbs.mm"
include "adantr.mm"
include "subgrcl.mm"
include "subgss.mm"
include "simprl.mm"
include "sseldd.mm"
include "simprr.mm"
include "grpinvadd.mm"
include "subginvcl.mm"
include "syl2anc.mm"
include "cntzi.mm"
include "eqtr4d.mm"
include "lsmelvali.mm"
include "syl22anc.mm"
include "eqeltrd.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "issubg3.mm"
include "mpbir2and.mm"

theorem lsmsubg
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x
  let vy: setvar y
  assume lsmsubg.p: |- .(+) = ( LSSum ` G )
  assume lsmsubg.z: |- Z = ( Cntz ` G )


  assert |- ( ( T e. ( SubGrp ` G ) /\ U e. ( SubGrp ` G ) /\ T C_ ( Z ` U ) ) -> ( T .(+) U ) e. ( SubGrp ` G ) )

  proof
    cT
    cG
    csubg
    cfv
    #
    wcel
    #
    cU
    @0
    wcel
    #
    cT
    cU
    cZ
    cfv
    #
    wss
    #
    w3a
    #
    cT
    cU
    c.po
    co
    #
    @0
    wcel
    #
    @6
    cG
    csubmnd
    cfv
    #
    wcel
    #
    vx
    cv
    #
    cG
    cminusg
    cfv
    #
    cfv
    #
    @6
    wcel
    #
    vx
    @6
    wral
    #
    @5
    cT
    @8
    wcel
    #
    cU
    @8
    wcel
    #
    @4
    @9
    @5
    @1
    @15
    @1
    @2
    @4
    simp1
    #
    cT
    cG
    subgsubm
    syl
    @5
    @2
    @16
    @1
    @2
    @4
    simp2
    #
    cU
    cG
    subgsubm
    syl
    @1
    @2
    @4
    simp3
    #
    c.po
    cT
    cU
    cG
    cZ
    lsmsubg.p
    lsmsubg.z
    lsmsubm
    syl3anc
    @5
    @13
    vx
    @6
    @5
    @10
    @6
    wcel
    #
    @10
    va
    cv
    #
    vb
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vb
    cU
    wrex
    va
    cT
    wrex
    #
    @13
    @1
    @2
    @20
    @26
    wb
    @4
    va
    vb
    @23
    c.po
    cT
    cU
    cG
    @10
    @23
    eqid
    #
    lsmsubg.p
    lsmelval
    3adant3
    @5
    @25
    @13
    va
    vb
    cT
    cU
    @5
    @21
    cT
    wcel
    #
    @22
    cU
    wcel
    #
    wa
    #
    wa
    #
    @13
    @25
    @24
    @11
    cfv
    #
    @6
    wcel
    @31
    @32
    @21
    @11
    cfv
    #
    @22
    @11
    cfv
    #
    @23
    co
    #
    @6
    @31
    @32
    @34
    @33
    @23
    co
    #
    @35
    @31
    cG
    cgrp
    wcel
    #
    @21
    cG
    cbs
    cfv
    #
    wcel
    @22
    @38
    wcel
    @32
    @36
    wceq
    @31
    @1
    @37
    @5
    @1
    @30
    @17
    adantr
    #
    cT
    cG
    subgrcl
    #
    syl
    @31
    cT
    @38
    @21
    @31
    @1
    cT
    @38
    wss
    @39
    @38
    cT
    cG
    @38
    eqid
    #
    subgss
    syl
    @5
    @28
    @29
    simprl
    #
    sseldd
    @31
    cU
    @38
    @22
    @31
    @2
    cU
    @38
    wss
    @5
    @2
    @30
    @18
    adantr
    #
    @38
    cU
    cG
    @41
    subgss
    syl
    @5
    @28
    @29
    simprr
    #
    sseldd
    @38
    @23
    cG
    @11
    @21
    @22
    @41
    @27
    @11
    eqid
    #
    grpinvadd
    syl3anc
    @31
    @33
    @3
    wcel
    @34
    cU
    wcel
    #
    @35
    @36
    wceq
    @31
    cT
    @3
    @33
    @5
    @4
    @30
    @19
    adantr
    @31
    @1
    @28
    @33
    cT
    wcel
    #
    @39
    @42
    cT
    cG
    @11
    @21
    @45
    subginvcl
    syl2anc
    #
    sseldd
    @31
    @2
    @29
    @46
    @43
    @44
    cU
    cG
    @11
    @22
    @45
    subginvcl
    syl2anc
    #
    @23
    cU
    cG
    @33
    @34
    cZ
    @27
    lsmsubg.z
    cntzi
    syl2anc
    eqtr4d
    @31
    @1
    @2
    @47
    @46
    @35
    @6
    wcel
    @39
    @43
    @48
    @49
    @23
    c.po
    cT
    cU
    cG
    @33
    @34
    @27
    lsmsubg.p
    lsmelvali
    syl22anc
    eqeltrd
    @25
    @12
    @32
    @6
    @10
    @24
    @11
    fveq2
    eleq1d
    syl5ibrcom
    rexlimdvva
    sylbid
    ralrimiv
    @5
    @37
    @7
    @9
    @14
    wa
    wb
    @5
    @1
    @37
    @17
    @40
    syl
    vx
    @6
    cG
    @11
    @45
    issubg3
    syl
    mpbir2and
end
