include "wcel.mm"
include "cv.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "wss.mm"
include "crab.mm"
include "cplusg.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "c0g.mm"
include "eqidd.mm"
include "cbs.mm"
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
include "0ss.mm"
include "eqsstri.mm"
include "syl6eqssr.mm"
include "difeq1.mm"
include "sseq1d.mm"
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
include "mvdco.mm"
include "simp2r.mm"
include "simp3r.mm"
include "unssd.mm"
include "syl5ss.mm"
include "eqsstrd.mm"
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

theorem symgsssg
  let vx: setvar x
  let cB: class B
  let cD: class D
  let cG: class G
  let cV: class V
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  assume symgsssg.g: |- G = ( SymGrp ` D )
  assume symgsssg.b: |- B = ( Base ` G )

  disjoint B x
  disjoint G x
  disjoint X x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint G y
  disjoint G z
  disjoint X y
  disjoint X z
  disjoint D y
  disjoint D z
  disjoint V y
  disjoint V z
  assert |- ( D e. V -> { x e. B | dom ( x \ _I ) C_ X } e. ( SubGrp ` G ) )

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
    cX
    wss
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
    cX
    wss
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
    cX
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
    cX
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
    cX
    0ss
    eqsstri
    syl6eqssr
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
    cX
    @19
    @2
    @11
    @1
    @8
    cid
    difeq1
    dmeqd
    sseq1d
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
    cX
    wss
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
    cX
    wss
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
    cX
    @35
    @2
    @23
    @1
    @20
    cid
    difeq1
    dmeqd
    sseq1d
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
    cX
    @37
    @2
    @29
    @1
    @27
    cid
    difeq1
    dmeqd
    sseq1d
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
    cX
    wss
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
    cX
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
    @48
    @24
    @30
    cun
    cX
    @20
    @27
    mvdco
    @38
    @24
    @30
    cX
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
    unssd
    syl5ss
    eqsstrd
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
    cX
    @49
    @2
    @40
    @1
    @33
    cid
    difeq1
    dmeqd
    sseq1d
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
    @51
    cB
    wcel
    #
    @51
    cid
    cdif
    #
    cdm
    #
    cX
    wss
    #
    @52
    @53
    @14
    @22
    @54
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
    @50
    @20
    symgsssg.b
    @50
    eqid
    #
    grpinvcl
    syl2anc
    @53
    @56
    @24
    cX
    @53
    @56
    @20
    ccnv
    #
    cid
    cdif
    #
    cdm
    #
    @24
    @53
    @55
    @60
    @53
    @51
    @59
    cid
    @22
    @51
    @59
    wceq
    @0
    @25
    cD
    cB
    @20
    cG
    @50
    symgsssg.g
    symgsssg.b
    @58
    symginv
    ad2antrl
    difeq1d
    dmeqd
    @53
    cD
    cD
    @20
    wf1o
    #
    @61
    @24
    wceq
    @22
    @62
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
    eqsstrd
    @4
    @57
    vx
    @51
    cB
    @1
    @51
    wceq
    #
    @3
    @56
    cX
    @63
    @2
    @55
    @1
    @51
    cid
    difeq1
    dmeqd
    sseq1d
    elrab
    sylanbrc
    sylan2b
    @15
    issubgrpd2
end
