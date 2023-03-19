include "cphl.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "cplusg.mm"
include "wral.mm"
include "csca.mm"
include "cbs.mm"
include "ocvss.mm"
include "a1i.mm"
include "c0g.mm"
include "cip.mm"
include "wceq.mm"
include "simpr.mm"
include "clmod.mm"
include "phllmod.mm"
include "adantr.mm"
include "eqid.mm"
include "lmod0vcl.mm"
include "syl.mm"
include "simpll.mm"
include "sselda.mm"
include "ip0l.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "elocv.mm"
include "syl3anbrc.mm"
include "ne0i.mm"
include "w3a.mm"
include "simpr1.mm"
include "simpr2.mm"
include "sseldi.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "simpr3.mm"
include "lmodvacl.mm"
include "adantlr.mm"
include "ipdir.mm"
include "syl13anc.mm"
include "cmulr.mm"
include "ipass.mm"
include "ocvi.mm"
include "sylan.mm"
include "oveq2d.mm"
include "crg.mm"
include "lmodring.mm"
include "ringrz.mm"
include "3eqtrd.mm"
include "oveq12d.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "grpidcl.mm"
include "grplid.mm"
include "mpdan.mm"
include "3syl.mm"
include "ralrimivvva.mm"
include "islss.mm"

theorem ocvlss
  let cS: class S
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ocvss.v: |- V = ( Base ` W )
  assume ocvss.o: |- ._|_ = ( ocv ` W )
  assume ocvlss.l: |- L = ( LSubSp ` W )


  assert |- ( ( W e. PreHil /\ S C_ V ) -> ( ._|_ ` S ) e. L )

  proof
    cW
    cphl
    wcel
    #
    cS
    cV
    wss
    #
    wa
    #
    cS
    c.pe
    cfv
    #
    cV
    wss
    #
    @3
    c0
    wne
    #
    vr
    cv
    #
    vy
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    vz
    cv
    #
    cW
    cplusg
    cfv
    #
    co
    #
    @3
    wcel
    #
    vz
    @3
    wral
    vy
    @3
    wral
    vr
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    wral
    @3
    cL
    wcel
    @4
    @2
    cS
    c.pe
    cV
    cW
    ocvss.v
    ocvss.o
    ocvss
    #
    a1i
    @2
    cW
    c0g
    cfv
    #
    @3
    wcel
    #
    @5
    @2
    @1
    @17
    cV
    wcel
    #
    @17
    vx
    cv
    #
    cW
    cip
    cfv
    #
    co
    @14
    c0g
    cfv
    #
    wceq
    #
    vx
    cS
    wral
    @18
    @0
    @1
    simpr
    #
    @2
    cW
    clmod
    wcel
    #
    @19
    @0
    @25
    @1
    cW
    phllmod
    adantr
    #
    cV
    cW
    @17
    ocvss.v
    @17
    eqid
    #
    lmod0vcl
    syl
    @2
    @23
    vx
    cS
    @2
    @20
    cS
    wcel
    #
    wa
    @0
    @20
    cV
    wcel
    #
    @23
    @0
    @1
    @28
    simpll
    #
    @2
    cS
    cV
    @20
    @24
    sselda
    #
    @20
    @14
    @21
    cV
    cW
    @17
    @22
    @14
    eqid
    #
    @21
    eqid
    #
    ocvss.v
    @22
    eqid
    #
    @27
    ip0l
    syl2anc
    ralrimiva
    vx
    @17
    cS
    @14
    @21
    c.pe
    cV
    cW
    @22
    ocvss.v
    @33
    @32
    @34
    ocvss.o
    elocv
    syl3anbrc
    @3
    @17
    ne0i
    syl
    @2
    @13
    vr
    vy
    vz
    @15
    @3
    @3
    @2
    @6
    @15
    wcel
    #
    @7
    @3
    wcel
    #
    @10
    @3
    wcel
    #
    w3a
    #
    wa
    #
    @1
    @12
    cV
    wcel
    #
    @12
    @20
    @21
    co
    #
    @22
    wceq
    #
    vx
    cS
    wral
    @13
    @2
    @1
    @38
    @24
    adantr
    @39
    @25
    @9
    cV
    wcel
    #
    @10
    cV
    wcel
    #
    @40
    @2
    @25
    @38
    @26
    adantr
    #
    @39
    @25
    @35
    @7
    cV
    wcel
    #
    @43
    @45
    @2
    @35
    @36
    @37
    simpr1
    #
    @39
    @3
    cV
    @7
    @16
    @2
    @35
    @36
    @37
    simpr2
    #
    sseldi
    #
    @6
    @8
    @14
    @15
    cV
    cW
    @7
    ocvss.v
    @32
    @8
    eqid
    #
    @15
    eqid
    #
    lmodvscl
    syl3anc
    #
    @39
    @3
    cV
    @10
    @16
    @2
    @35
    @36
    @37
    simpr3
    #
    sseldi
    #
    @11
    cV
    cW
    @9
    @10
    ocvss.v
    @11
    eqid
    #
    lmodvacl
    syl3anc
    @39
    @42
    vx
    cS
    @39
    @28
    wa
    #
    @41
    @9
    @20
    @21
    co
    #
    @10
    @20
    @21
    co
    #
    @14
    cplusg
    cfv
    #
    co
    #
    @22
    @22
    @59
    co
    #
    @22
    @56
    @0
    @43
    @44
    @29
    @41
    @60
    wceq
    @2
    @28
    @0
    @38
    @30
    adantlr
    #
    @39
    @43
    @28
    @52
    adantr
    @39
    @44
    @28
    @54
    adantr
    @2
    @28
    @29
    @38
    @31
    adantlr
    #
    @9
    @10
    @20
    @11
    @59
    @14
    @21
    cV
    cW
    @32
    @33
    ocvss.v
    @55
    @59
    eqid
    #
    ipdir
    syl13anc
    @56
    @57
    @22
    @58
    @22
    @59
    @56
    @57
    @6
    @7
    @20
    @21
    co
    #
    @14
    cmulr
    cfv
    #
    co
    #
    @6
    @22
    @66
    co
    #
    @22
    @56
    @0
    @35
    @46
    @29
    @57
    @67
    wceq
    @62
    @39
    @35
    @28
    @47
    adantr
    #
    @39
    @46
    @28
    @49
    adantr
    @63
    @6
    @7
    @20
    @8
    @66
    @14
    @21
    @15
    cV
    cW
    @32
    @33
    ocvss.v
    @51
    @50
    @66
    eqid
    #
    ipass
    syl13anc
    @56
    @65
    @22
    @6
    @66
    @39
    @36
    @28
    @65
    @22
    wceq
    @48
    @7
    @20
    cS
    @14
    @21
    c.pe
    cV
    cW
    @22
    ocvss.v
    @33
    @32
    @34
    ocvss.o
    ocvi
    sylan
    oveq2d
    @56
    @14
    crg
    wcel
    #
    @35
    @68
    @22
    wceq
    @56
    @25
    @71
    @39
    @25
    @28
    @45
    adantr
    #
    @14
    cW
    @32
    lmodring
    syl
    @69
    @15
    @14
    @66
    @6
    @22
    @51
    @70
    @34
    ringrz
    syl2anc
    3eqtrd
    @39
    @37
    @28
    @58
    @22
    wceq
    @53
    @10
    @20
    cS
    @14
    @21
    c.pe
    cV
    cW
    @22
    ocvss.v
    @33
    @32
    @34
    ocvss.o
    ocvi
    sylan
    oveq12d
    @56
    @25
    @14
    cgrp
    wcel
    #
    @61
    @22
    wceq
    #
    @72
    @14
    cW
    @32
    lmodfgrp
    @73
    @22
    @15
    wcel
    @74
    @15
    @14
    @22
    @51
    @34
    grpidcl
    @15
    @59
    @14
    @22
    @22
    @51
    @64
    @34
    grplid
    mpdan
    3syl
    3eqtrd
    ralrimiva
    vx
    @12
    cS
    @14
    @21
    c.pe
    cV
    cW
    @22
    ocvss.v
    @33
    @32
    @34
    ocvss.o
    elocv
    syl3anbrc
    ralrimivvva
    vr
    @15
    @11
    cL
    @8
    @3
    @14
    cV
    cW
    vy
    vz
    @32
    @51
    ocvss.v
    @55
    @50
    ocvlss.l
    islss
    syl3anbrc
end
