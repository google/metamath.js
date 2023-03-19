include "wcel.mm"
include "cv.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "cfn.mm"
include "crab.mm"
include "cplusg.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "c0g.mm"
include "eqidd.mm"
include "cbs.mm"
include "wss.mm"
include "ssrab2.mm"
include "sseqtri.mm"
include "a1i.mm"
include "cgrp.mm"
include "symggrp.mm"
include "eqid.mm"
include "grpidcl.mm"
include "syl.mm"
include "cres.mm"
include "symgid.mm"
include "difeq1d.mm"
include "dmeqd.mm"
include "c0.mm"
include "wceq.mm"
include "resss.mm"
include "ssdif0.mm"
include "mpbi.mm"
include "dmeqi.mm"
include "dm0.mm"
include "eqtri.mm"
include "0fin.mm"
include "eqeltri.mm"
include "syl6eqelr.mm"
include "difeq1.mm"
include "eleq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "wa.mm"
include "biid.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp2l.mm"
include "simp3l.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "ccom.mm"
include "symgov.mm"
include "syl2anc.mm"
include "cun.mm"
include "simp2r.mm"
include "simp3r.mm"
include "unfi.mm"
include "mvdco.mm"
include "ssfi.mm"
include "sylancl.mm"
include "eqeltrd.mm"
include "syl3anb.mm"
include "cminusg.mm"
include "adantr.mm"
include "simprl.mm"
include "grpinvcl.mm"
include "ccnv.mm"
include "symginv.mm"
include "ad2antrl.mm"
include "wf1o.mm"
include "symgbasf1o.mm"
include "f1omvdcnv.mm"
include "eqtrd.mm"
include "simprr.mm"
include "sylan2b.mm"
include "issubgrpd2.mm"

theorem symgfisg
  let vx: setvar x
  let cB: class B
  let cD: class D
  let cG: class G
  let cV: class V
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  assume symgsssg.g: |- G = ( SymGrp ` D )
  assume symgsssg.b: |- B = ( Base ` G )

  disjoint B x
  disjoint G x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint G y
  disjoint G z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint D y
  disjoint D z
  disjoint V y
  disjoint V z
  assert |- ( D e. V -> { x e. B | dom ( x \ _I ) e. Fin } e. ( SubGrp ` G ) )

  proof
    cD
    cV
    wcel
    #
    vy
    vz
    vx
    cv
    #
    cid
    cdif
    #
    cdm
    #
    cfn
    wcel
    #
    vx
    cB
    crab
    #
    cG
    cplusg
    cfv
    #
    cG
    @5
    cress
    co
    #
    cG
    cG
    c0g
    cfv
    #
    @0
    @7
    eqidd
    @0
    @8
    eqidd
    @0
    @6
    eqidd
    @5
    cG
    cbs
    cfv
    #
    wss
    @0
    @5
    cB
    @9
    @4
    vx
    cB
    ssrab2
    symgsssg.b
    sseqtri
    a1i
    @0
    @8
    cB
    wcel
    #
    @8
    cid
    cdif
    #
    cdm
    #
    cfn
    wcel
    #
    @8
    @5
    wcel
    @0
    cG
    cgrp
    wcel
    #
    @10
    cD
    cG
    cV
    symgsssg.g
    symggrp
    #
    cB
    cG
    @8
    symgsssg.b
    @8
    eqid
    grpidcl
    syl
    @0
    @12
    cid
    cD
    cres
    #
    cid
    cdif
    #
    cdm
    #
    cfn
    @0
    @17
    @11
    @0
    @16
    @8
    cid
    cD
    cG
    cV
    symgsssg.g
    symgid
    difeq1d
    dmeqd
    @18
    c0
    cfn
    @18
    c0
    cdm
    c0
    @17
    c0
    @16
    cid
    wss
    @17
    c0
    wceq
    cid
    cD
    resss
    @16
    cid
    ssdif0
    mpbi
    dmeqi
    dm0
    eqtri
    0fin
    eqeltri
    syl6eqelr
    @4
    @13
    vx
    @8
    cB
    @1
    @8
    wceq
    #
    @3
    @12
    cfn
    @19
    @2
    @11
    @1
    @8
    cid
    difeq1
    dmeqd
    eleq1d
    elrab
    sylanbrc
    @0
    @0
    vy
    cv
    #
    @5
    wcel
    #
    @20
    cB
    wcel
    #
    @20
    cid
    cdif
    #
    cdm
    #
    cfn
    wcel
    #
    wa
    #
    vz
    cv
    #
    @5
    wcel
    @27
    cB
    wcel
    #
    @27
    cid
    cdif
    #
    cdm
    #
    cfn
    wcel
    #
    wa
    #
    @20
    @27
    @6
    co
    #
    @5
    wcel
    #
    @0
    biid
    @4
    @25
    vx
    @20
    cB
    @1
    @20
    wceq
    #
    @3
    @24
    cfn
    @35
    @2
    @23
    @1
    @20
    cid
    difeq1
    dmeqd
    eleq1d
    elrab
    #
    @4
    @31
    vx
    @27
    cB
    @1
    @27
    wceq
    #
    @3
    @30
    cfn
    @37
    @2
    @29
    @1
    @27
    cid
    difeq1
    dmeqd
    eleq1d
    elrab
    @0
    @26
    @32
    w3a
    #
    @33
    cB
    wcel
    #
    @33
    cid
    cdif
    #
    cdm
    #
    cfn
    wcel
    #
    @34
    @38
    @14
    @22
    @28
    @39
    @0
    @26
    @14
    @32
    @15
    3ad2ant1
    @0
    @22
    @25
    @32
    simp2l
    #
    @0
    @26
    @28
    @31
    simp3l
    #
    cB
    @6
    cG
    @20
    @27
    symgsssg.b
    @6
    eqid
    #
    grpcl
    syl3anc
    @38
    @41
    @20
    @27
    ccom
    #
    cid
    cdif
    #
    cdm
    #
    cfn
    @38
    @40
    @47
    @38
    @33
    @46
    cid
    @38
    @22
    @28
    @33
    @46
    wceq
    @43
    @44
    cD
    cB
    @6
    cG
    @20
    @27
    symgsssg.g
    symgsssg.b
    @45
    symgov
    syl2anc
    difeq1d
    dmeqd
    @38
    @24
    @30
    cun
    #
    cfn
    wcel
    #
    @48
    @49
    wss
    @48
    cfn
    wcel
    @38
    @25
    @31
    @50
    @0
    @22
    @25
    @32
    simp2r
    @0
    @26
    @28
    @31
    simp3r
    @24
    @30
    unfi
    syl2anc
    @20
    @27
    mvdco
    @49
    @48
    ssfi
    sylancl
    eqeltrd
    @4
    @42
    vx
    @33
    cB
    @1
    @33
    wceq
    #
    @3
    @41
    cfn
    @51
    @2
    @40
    @1
    @33
    cid
    difeq1
    dmeqd
    eleq1d
    elrab
    sylanbrc
    syl3anb
    @21
    @0
    @26
    @20
    cG
    cminusg
    cfv
    #
    cfv
    #
    @5
    wcel
    #
    @36
    @0
    @26
    wa
    #
    @53
    cB
    wcel
    #
    @53
    cid
    cdif
    #
    cdm
    #
    cfn
    wcel
    #
    @54
    @55
    @14
    @22
    @56
    @0
    @14
    @26
    @15
    adantr
    @0
    @22
    @25
    simprl
    cB
    cG
    @52
    @20
    symgsssg.b
    @52
    eqid
    #
    grpinvcl
    syl2anc
    @55
    @58
    @24
    cfn
    @55
    @58
    @20
    ccnv
    #
    cid
    cdif
    #
    cdm
    #
    @24
    @55
    @57
    @62
    @55
    @53
    @61
    cid
    @22
    @53
    @61
    wceq
    @0
    @25
    cD
    cB
    @20
    cG
    @52
    symgsssg.g
    symgsssg.b
    @60
    symginv
    ad2antrl
    difeq1d
    dmeqd
    @55
    cD
    cD
    @20
    wf1o
    #
    @63
    @24
    wceq
    @22
    @64
    @0
    @25
    cD
    cB
    @20
    cG
    symgsssg.g
    symgsssg.b
    symgbasf1o
    ad2antrl
    cD
    @20
    f1omvdcnv
    syl
    eqtrd
    @0
    @22
    @25
    simprr
    eqeltrd
    @4
    @59
    vx
    @53
    cB
    @1
    @53
    wceq
    #
    @3
    @58
    cfn
    @65
    @2
    @57
    @1
    @53
    cid
    difeq1
    dmeqd
    eleq1d
    elrab
    sylanbrc
    sylan2b
    @15
    issubgrpd2
end
