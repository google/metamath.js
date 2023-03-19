include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "wss.mm"
include "wa.mm"
include "cin.mm"
include "co.mm"
include "simpl1.mm"
include "simpl2.mm"
include "inss1.mm"
include "a1i.mm"
include "lsmless2.mm"
include "syl3anc.mm"
include "simpr.mm"
include "inss2.mm"
include "wb.mm"
include "cbs.mm"
include "cmre.mm"
include "cgrp.mm"
include "cacs.mm"
include "subgrcl.mm"
include "eqid.mm"
include "subgacs.mm"
include "acsmre.mm"
include "4syl.mm"
include "simpl3.mm"
include "mreincl.mm"
include "lsmlub.mm"
include "mpbi2and.mm"
include "ssind.mm"
include "cv.mm"
include "elin.mm"
include "cplusg.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "lsmelval.mm"
include "syl2anc.mm"
include "adantr.mm"
include "simprll.mm"
include "simprlr.mm"
include "cminusg.mm"
include "c0g.mm"
include "syl.mm"
include "subgss.mm"
include "sseldd.mm"
include "grplinv.mm"
include "oveq1d.mm"
include "subginvcl.mm"
include "simpll2.mm"
include "grpass.mm"
include "syl13anc.mm"
include "grplid.mm"
include "3eqtr3d.mm"
include "simprr.mm"
include "subgcl.mm"
include "eqeltrrd.mm"
include "elind.mm"
include "lsmelvali.mm"
include "syl22anc.mm"
include "expr.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "sylbid.mm"
include "impd.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem lsmmod
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cU: class U
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lsmmod.p: |- .(+) = ( LSSum ` G )


  assert |- ( ( ( S e. ( SubGrp ` G ) /\ T e. ( SubGrp ` G ) /\ U e. ( SubGrp ` G ) ) /\ S C_ U ) -> ( S .(+) ( T i^i U ) ) = ( ( S .(+) T ) i^i U ) )

  proof
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    cT
    @0
    wcel
    #
    cU
    @0
    wcel
    #
    w3a
    #
    cS
    cU
    wss
    #
    wa
    #
    cS
    cT
    cU
    cin
    #
    c.po
    co
    #
    cS
    cT
    c.po
    co
    #
    cU
    cin
    #
    @6
    @8
    @9
    cU
    @6
    @1
    @2
    @7
    cT
    wss
    #
    @8
    @9
    wss
    @1
    @2
    @3
    @5
    simpl1
    #
    @1
    @2
    @3
    @5
    simpl2
    #
    @11
    @6
    cT
    cU
    inss1
    a1i
    c.po
    cS
    @7
    cT
    cG
    lsmmod.p
    lsmless2
    syl3anc
    @6
    @5
    @7
    cU
    wss
    #
    @8
    cU
    wss
    #
    @4
    @5
    simpr
    #
    @14
    @6
    cT
    cU
    inss2
    a1i
    @6
    @1
    @7
    @0
    wcel
    #
    @3
    @5
    @14
    wa
    @15
    wb
    @12
    @6
    @0
    cG
    cbs
    cfv
    #
    cmre
    cfv
    wcel
    #
    @2
    @3
    @17
    @6
    @1
    cG
    cgrp
    wcel
    #
    @0
    @18
    cacs
    cfv
    wcel
    @19
    @12
    cS
    cG
    subgrcl
    #
    @18
    cG
    @18
    eqid
    #
    subgacs
    @0
    @18
    acsmre
    4syl
    @13
    @1
    @2
    @3
    @5
    simpl3
    #
    cT
    cU
    @0
    @18
    mreincl
    syl3anc
    #
    @23
    c.po
    cS
    @7
    cU
    cG
    lsmmod.p
    lsmlub
    syl3anc
    mpbi2and
    ssind
    @6
    vx
    @10
    @8
    vx
    cv
    #
    @10
    wcel
    @25
    @9
    wcel
    #
    @25
    cU
    wcel
    #
    wa
    @6
    @25
    @8
    wcel
    #
    @25
    @9
    cU
    elin
    @6
    @26
    @27
    @28
    @6
    @26
    @25
    vy
    cv
    #
    vz
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
    vz
    cT
    wrex
    vy
    cS
    wrex
    #
    @27
    @28
    wi
    #
    @6
    @1
    @2
    @26
    @34
    wb
    @12
    @13
    vy
    vz
    @31
    c.po
    cS
    cT
    cG
    @25
    @31
    eqid
    #
    lsmmod.p
    lsmelval
    syl2anc
    @6
    @33
    @35
    vy
    vz
    cS
    cT
    @6
    @29
    cS
    wcel
    #
    @30
    cT
    wcel
    #
    wa
    #
    wa
    @35
    @33
    @32
    cU
    wcel
    #
    @32
    @8
    wcel
    #
    wi
    @6
    @39
    @40
    @41
    @6
    @39
    @40
    wa
    #
    wa
    #
    @1
    @17
    @37
    @30
    @7
    wcel
    @41
    @6
    @1
    @42
    @12
    adantr
    #
    @6
    @17
    @42
    @24
    adantr
    @6
    @37
    @38
    @40
    simprll
    #
    @43
    cT
    cU
    @30
    @6
    @37
    @38
    @40
    simprlr
    #
    @43
    @29
    cG
    cminusg
    cfv
    #
    cfv
    #
    @32
    @31
    co
    #
    @30
    cU
    @43
    @48
    @29
    @31
    co
    #
    @30
    @31
    co
    #
    cG
    c0g
    cfv
    #
    @30
    @31
    co
    #
    @49
    @30
    @43
    @50
    @52
    @30
    @31
    @43
    @20
    @29
    @18
    wcel
    #
    @50
    @52
    wceq
    @43
    @1
    @20
    @44
    @21
    syl
    #
    @43
    cU
    @18
    @29
    @43
    @3
    cU
    @18
    wss
    @6
    @3
    @42
    @23
    adantr
    #
    @18
    cU
    cG
    @22
    subgss
    syl
    #
    @43
    cS
    cU
    @29
    @6
    @5
    @42
    @16
    adantr
    @45
    sseldd
    #
    sseldd
    #
    @18
    @31
    cG
    @47
    @29
    @52
    @22
    @36
    @52
    eqid
    #
    @47
    eqid
    #
    grplinv
    syl2anc
    oveq1d
    @43
    @20
    @48
    @18
    wcel
    @54
    @30
    @18
    wcel
    #
    @51
    @49
    wceq
    @55
    @43
    cU
    @18
    @48
    @57
    @43
    @3
    @29
    cU
    wcel
    @48
    cU
    wcel
    #
    @56
    @58
    cU
    cG
    @47
    @29
    @61
    subginvcl
    syl2anc
    #
    sseldd
    @59
    @43
    cT
    @18
    @30
    @43
    @2
    cT
    @18
    wss
    @1
    @2
    @3
    @5
    @42
    simpll2
    @18
    cT
    cG
    @22
    subgss
    syl
    @46
    sseldd
    #
    @18
    @31
    cG
    @48
    @29
    @30
    @22
    @36
    grpass
    syl13anc
    @43
    @20
    @62
    @53
    @30
    wceq
    @55
    @65
    @18
    @31
    cG
    @30
    @52
    @22
    @36
    @60
    grplid
    syl2anc
    3eqtr3d
    @43
    @3
    @63
    @40
    @49
    cU
    wcel
    @56
    @64
    @6
    @39
    @40
    simprr
    @31
    cU
    cG
    @48
    @32
    @36
    subgcl
    syl3anc
    eqeltrrd
    elind
    @31
    c.po
    cS
    @7
    cG
    @29
    @30
    @36
    lsmmod.p
    lsmelvali
    syl22anc
    expr
    @33
    @27
    @40
    @28
    @41
    @25
    @32
    cU
    eleq1
    @25
    @32
    @8
    eleq1
    imbi12d
    syl5ibrcom
    rexlimdvva
    sylbid
    impd
    syl5bi
    ssrdv
    eqssd
end
