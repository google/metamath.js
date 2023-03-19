include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "lssss.mm"
include "adantl.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "cplusg.mm"
include "cvsca.mm"
include "cmulr.mm"
include "cur.mm"
include "wceq.mm"
include "ressbas2.mm"
include "sylan2.mm"
include "eqid.mm"
include "ressplusg.mm"
include "resssca.mm"
include "ressvsca.mm"
include "eqidd.mm"
include "crg.mm"
include "lmodring.mm"
include "adantr.mm"
include "csubg.mm"
include "cgrp.mm"
include "lsssubg.mm"
include "subggrp.mm"
include "syl.mm"
include "cv.mm"
include "co.mm"
include "lssvscl.mm"
include "3impb.mm"
include "w3a.mm"
include "simpll.mm"
include "simpr1.mm"
include "ad2antlr.mm"
include "simpr2.mm"
include "sseldd.mm"
include "simpr3.mm"
include "lmodvsdi.mm"
include "syl13anc.mm"
include "lmodvsdir.mm"
include "lmodvsass.mm"
include "sselda.mm"
include "lmodvs1.mm"
include "adantlr.mm"
include "syldan.mm"
include "islmodd.mm"
include "jca.mm"
include "simprl.mm"
include "cvv.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "eqcomd.mm"
include "a1i.mm"
include "clss.mm"
include "eqsstr3d.mm"
include "c0.mm"
include "wne.mm"
include "lmodgrp.mm"
include "ad2antll.mm"
include "grpbn0.mm"
include "lss1.mm"
include "lsscl.mm"
include "sylan.mm"
include "islssd.mm"
include "eqeltrd.mm"
include "impbida.mm"

theorem islss3
  let cS: class S
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  assume islss3.x: |- X = ( W |`s U )
  assume islss3.v: |- V = ( Base ` W )
  assume islss3.s: |- S = ( LSubSp ` W )


  assert |- ( W e. LMod -> ( U e. S <-> ( U C_ V /\ X e. LMod ) ) )

  proof
    cW
    clmod
    wcel
    #
    cU
    cS
    wcel
    #
    cU
    cV
    wss
    #
    cX
    clmod
    wcel
    #
    wa
    #
    @0
    @1
    wa
    #
    @2
    @3
    @1
    @2
    @0
    cS
    cU
    cV
    cW
    islss3.v
    islss3.s
    lssss
    #
    adantl
    #
    @5
    vx
    va
    vb
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    cW
    cplusg
    cfv
    #
    @8
    cplusg
    cfv
    #
    cW
    cvsca
    cfv
    #
    @8
    cmulr
    cfv
    #
    @8
    cur
    cfv
    #
    @8
    cU
    cX
    @1
    @0
    @2
    cU
    cX
    cbs
    cfv
    #
    wceq
    #
    @6
    @2
    @16
    @0
    cU
    cV
    cX
    cW
    islss3.x
    islss3.v
    ressbas2
    #
    adantl
    sylan2
    @1
    @10
    cX
    cplusg
    cfv
    #
    wceq
    #
    @0
    cU
    @10
    cW
    cX
    cS
    islss3.x
    @10
    eqid
    #
    ressplusg
    adantl
    @1
    @8
    cX
    csca
    cfv
    #
    wceq
    #
    @0
    cU
    @8
    cW
    cX
    cS
    islss3.x
    @8
    eqid
    #
    resssca
    adantl
    @1
    @12
    cX
    cvsca
    cfv
    #
    wceq
    #
    @0
    cU
    @12
    cW
    cX
    cS
    islss3.x
    @12
    eqid
    #
    ressvsca
    adantl
    @5
    @9
    eqidd
    @5
    @11
    eqidd
    @5
    @13
    eqidd
    @5
    @14
    eqidd
    @0
    @8
    crg
    wcel
    @1
    @8
    cW
    @23
    lmodring
    adantr
    @5
    cU
    cW
    csubg
    cfv
    wcel
    cX
    cgrp
    wcel
    #
    cS
    cU
    cW
    islss3.s
    lsssubg
    cU
    cW
    cX
    islss3.x
    subggrp
    syl
    @5
    vx
    cv
    #
    @9
    wcel
    #
    va
    cv
    #
    cU
    wcel
    #
    @28
    @30
    @12
    co
    #
    cU
    wcel
    @9
    cS
    @12
    cU
    @8
    cW
    @28
    @30
    @23
    @26
    @9
    eqid
    #
    islss3.s
    lssvscl
    3impb
    @5
    @29
    @31
    vb
    cv
    #
    cU
    wcel
    #
    w3a
    #
    wa
    #
    @0
    @29
    @30
    cV
    wcel
    @34
    cV
    wcel
    #
    @28
    @30
    @34
    @10
    co
    @12
    co
    @32
    @28
    @34
    @12
    co
    #
    @10
    co
    wceq
    @0
    @1
    @36
    simpll
    @5
    @29
    @31
    @35
    simpr1
    @37
    cU
    cV
    @30
    @1
    @2
    @0
    @36
    @6
    ad2antlr
    #
    @5
    @29
    @31
    @35
    simpr2
    sseldd
    @37
    cU
    cV
    @34
    @40
    @5
    @29
    @31
    @35
    simpr3
    sseldd
    @10
    @28
    @12
    @8
    @9
    cV
    cW
    @30
    @34
    islss3.v
    @20
    @23
    @26
    @33
    lmodvsdi
    syl13anc
    @5
    @29
    @30
    @9
    wcel
    #
    @35
    w3a
    #
    wa
    #
    @0
    @29
    @41
    @38
    @28
    @30
    @11
    co
    @34
    @12
    co
    @39
    @30
    @34
    @12
    co
    #
    @10
    co
    wceq
    @0
    @1
    @42
    simpll
    #
    @5
    @29
    @41
    @35
    simpr1
    #
    @5
    @29
    @41
    @35
    simpr2
    #
    @43
    cU
    cV
    @34
    @1
    @2
    @0
    @42
    @6
    ad2antlr
    @5
    @29
    @41
    @35
    simpr3
    sseldd
    #
    @10
    @11
    @28
    @30
    @12
    @8
    @9
    cV
    cW
    @34
    islss3.v
    @20
    @23
    @26
    @33
    @11
    eqid
    lmodvsdir
    syl13anc
    @43
    @0
    @29
    @41
    @38
    @28
    @30
    @13
    co
    @34
    @12
    co
    @28
    @44
    @12
    co
    wceq
    @45
    @46
    @47
    @48
    @28
    @30
    @12
    @13
    @8
    @9
    cV
    cW
    @34
    islss3.v
    @23
    @26
    @33
    @13
    eqid
    lmodvsass
    syl13anc
    @5
    @28
    cU
    wcel
    @28
    cV
    wcel
    #
    @14
    @28
    @12
    co
    @28
    wceq
    #
    @5
    cU
    cV
    @28
    @7
    sselda
    @0
    @49
    @50
    @1
    @12
    @14
    @8
    cV
    cW
    @28
    islss3.v
    @23
    @26
    @14
    eqid
    lmodvs1
    adantlr
    syldan
    islmodd
    jca
    @0
    @4
    wa
    #
    cU
    @15
    cS
    @51
    @2
    @16
    @0
    @2
    @3
    simprl
    #
    @17
    syl
    #
    @51
    vx
    @21
    cbs
    cfv
    #
    @18
    cS
    @24
    @15
    @21
    cV
    cW
    va
    vb
    @51
    @8
    @21
    @51
    cU
    cvv
    wcel
    #
    @22
    @51
    cU
    @15
    cvv
    @53
    cX
    cbs
    fvex
    syl6eqel
    #
    cU
    @8
    cW
    cX
    cvv
    islss3.x
    @23
    resssca
    syl
    eqcomd
    @51
    @54
    eqidd
    cV
    cW
    cbs
    cfv
    wceq
    @51
    islss3.v
    a1i
    @51
    @10
    @18
    @51
    @55
    @19
    @56
    cU
    @10
    cW
    cX
    cvv
    islss3.x
    @20
    ressplusg
    syl
    eqcomd
    @51
    @12
    @24
    @51
    @55
    @25
    @56
    cU
    @12
    cW
    cX
    cvv
    islss3.x
    @26
    ressvsca
    syl
    eqcomd
    cS
    cW
    clss
    cfv
    wceq
    @51
    islss3.s
    a1i
    @51
    @15
    cU
    cV
    @53
    @52
    eqsstr3d
    @51
    @27
    @15
    c0
    wne
    @3
    @27
    @0
    @2
    cX
    lmodgrp
    ad2antll
    @15
    cX
    @15
    eqid
    #
    grpbn0
    syl
    @51
    @15
    cX
    clss
    cfv
    #
    wcel
    #
    @28
    @54
    wcel
    @30
    @15
    wcel
    @34
    @15
    wcel
    w3a
    @28
    @30
    @24
    co
    @34
    @18
    co
    @15
    wcel
    @3
    @59
    @0
    @2
    @58
    @15
    cX
    @57
    @58
    eqid
    #
    lss1
    ad2antll
    @54
    @18
    @58
    @24
    @15
    @21
    cX
    @30
    @34
    @28
    @21
    eqid
    @54
    eqid
    @18
    eqid
    @24
    eqid
    @60
    lsscl
    sylan
    islssd
    eqeltrd
    impbida
end
