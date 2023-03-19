include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "co.mm"
include "cbs.mm"
include "c0g.mm"
include "cv.mm"
include "cplusg.mm"
include "wral.mm"
include "cmnd.mm"
include "submrcl.mm"
include "3ad2ant1.mm"
include "eqid.mm"
include "submss.mm"
include "3ad2ant2.mm"
include "lsmssv.mm"
include "syl3anc.mm"
include "simp2.mm"
include "lsmub1x.mm"
include "syl2anc.mm"
include "subm0cl.mm"
include "sseldd.mm"
include "wa.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "lsmelvalx.mm"
include "anbi12d.mm"
include "reeanv.mm"
include "wi.mm"
include "adantr.mm"
include "simprll.mm"
include "simprlr.mm"
include "simprrl.mm"
include "simprrr.mm"
include "simpl3.mm"
include "cntzi.mm"
include "mnd4g.mm"
include "simpl1.mm"
include "submcl.mm"
include "simpl2.mm"
include "lsmelvalix.mm"
include "syl32anc.mm"
include "eqeltrrd.mm"
include "oveq12.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "anassrs.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "sylbid.mm"
include "ralrimivv.mm"
include "issubm.mm"
include "syl.mm"
include "mpbir3and.mm"

theorem lsmsubm
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


  assert |- ( ( T e. ( SubMnd ` G ) /\ U e. ( SubMnd ` G ) /\ T C_ ( Z ` U ) ) -> ( T .(+) U ) e. ( SubMnd ` G ) )

  proof
    cT
    cG
    csubmnd
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
    cbs
    cfv
    #
    wss
    #
    cG
    c0g
    cfv
    #
    @6
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @6
    wcel
    #
    vy
    @6
    wral
    vx
    @6
    wral
    #
    @5
    cG
    cmnd
    wcel
    #
    cT
    @8
    wss
    #
    cU
    @8
    wss
    #
    @9
    @1
    @2
    @18
    @4
    cT
    cG
    submrcl
    3ad2ant1
    #
    @1
    @2
    @19
    @4
    @8
    cT
    cG
    @8
    eqid
    #
    submss
    3ad2ant1
    #
    @2
    @1
    @20
    @4
    @8
    cU
    cG
    @22
    submss
    3ad2ant2
    #
    @8
    c.po
    cT
    cU
    cG
    @22
    lsmsubg.p
    lsmssv
    syl3anc
    @5
    cT
    @6
    @10
    @5
    @19
    @2
    cT
    @6
    wss
    @23
    @1
    @2
    @4
    simp2
    @8
    c.po
    cT
    cU
    cG
    @22
    lsmsubg.p
    lsmub1x
    syl2anc
    @1
    @2
    @10
    cT
    wcel
    @4
    cT
    cG
    @10
    @10
    eqid
    #
    subm0cl
    3ad2ant1
    sseldd
    @5
    @16
    vx
    vy
    @6
    @6
    @5
    @12
    @6
    wcel
    #
    @13
    @6
    wcel
    #
    wa
    @12
    va
    cv
    #
    vc
    cv
    #
    @14
    co
    #
    wceq
    #
    vc
    cU
    wrex
    #
    va
    cT
    wrex
    #
    @13
    vb
    cv
    #
    vd
    cv
    #
    @14
    co
    #
    wceq
    #
    vd
    cU
    wrex
    #
    vb
    cT
    wrex
    #
    wa
    #
    @16
    @5
    @26
    @33
    @27
    @39
    @5
    @18
    @19
    @20
    @26
    @33
    wb
    @21
    @23
    @24
    va
    vc
    @8
    @14
    c.po
    cT
    cU
    cG
    cmnd
    @12
    @22
    @14
    eqid
    #
    lsmsubg.p
    lsmelvalx
    syl3anc
    @5
    @18
    @19
    @20
    @27
    @39
    wb
    @21
    @23
    @24
    vb
    vd
    @8
    @14
    c.po
    cT
    cU
    cG
    cmnd
    @13
    @22
    @41
    lsmsubg.p
    lsmelvalx
    syl3anc
    anbi12d
    @40
    @32
    @38
    wa
    #
    vb
    cT
    wrex
    va
    cT
    wrex
    @5
    @16
    @32
    @38
    va
    vb
    cT
    cT
    reeanv
    @5
    @42
    @16
    va
    vb
    cT
    cT
    @42
    @31
    @37
    wa
    #
    vd
    cU
    wrex
    vc
    cU
    wrex
    @5
    @28
    cT
    wcel
    #
    @34
    cT
    wcel
    #
    wa
    #
    wa
    #
    @16
    @31
    @37
    vc
    vd
    cU
    cU
    reeanv
    @47
    @43
    @16
    vc
    vd
    cU
    cU
    @5
    @46
    @29
    cU
    wcel
    #
    @35
    cU
    wcel
    #
    wa
    #
    @43
    @16
    wi
    @5
    @46
    @50
    wa
    #
    wa
    #
    @16
    @43
    @30
    @36
    @14
    co
    #
    @6
    wcel
    @52
    @28
    @34
    @14
    co
    #
    @29
    @35
    @14
    co
    #
    @14
    co
    #
    @53
    @6
    @52
    @8
    @14
    cG
    @35
    @28
    @34
    @29
    @22
    @41
    @5
    @18
    @51
    @21
    adantr
    #
    @52
    cT
    @8
    @28
    @5
    @19
    @51
    @23
    adantr
    #
    @5
    @44
    @45
    @50
    simprll
    #
    sseldd
    @52
    cT
    @8
    @34
    @58
    @5
    @44
    @45
    @50
    simprlr
    #
    sseldd
    @52
    cU
    @8
    @29
    @5
    @20
    @51
    @24
    adantr
    #
    @5
    @46
    @48
    @49
    simprrl
    #
    sseldd
    @52
    cU
    @8
    @35
    @61
    @5
    @46
    @48
    @49
    simprrr
    #
    sseldd
    @52
    @34
    @3
    wcel
    @48
    @34
    @29
    @14
    co
    @29
    @34
    @14
    co
    wceq
    @52
    cT
    @3
    @34
    @1
    @2
    @4
    @51
    simpl3
    @60
    sseldd
    @62
    @14
    cU
    cG
    @34
    @29
    cZ
    @41
    lsmsubg.z
    cntzi
    syl2anc
    mnd4g
    @52
    @18
    @19
    @20
    @54
    cT
    wcel
    #
    @55
    cU
    wcel
    #
    @56
    @6
    wcel
    @57
    @58
    @61
    @52
    @1
    @44
    @45
    @64
    @1
    @2
    @4
    @51
    simpl1
    @59
    @60
    @14
    cT
    cG
    @28
    @34
    @41
    submcl
    syl3anc
    @52
    @2
    @48
    @49
    @65
    @1
    @2
    @4
    @51
    simpl2
    @62
    @63
    @14
    cU
    cG
    @29
    @35
    @41
    submcl
    syl3anc
    @8
    @14
    c.po
    cT
    cU
    cG
    cmnd
    @54
    @55
    @22
    @41
    lsmsubg.p
    lsmelvalix
    syl32anc
    eqeltrrd
    @43
    @15
    @53
    @6
    @12
    @30
    @13
    @36
    @14
    oveq12
    eleq1d
    syl5ibrcom
    anassrs
    rexlimdvva
    syl5bir
    rexlimdvva
    syl5bir
    sylbid
    ralrimivv
    @5
    @18
    @7
    @9
    @11
    @17
    w3a
    wb
    @21
    vx
    vy
    @8
    @14
    @6
    cG
    @10
    @22
    @25
    @41
    issubm
    syl
    mpbir3and
end
