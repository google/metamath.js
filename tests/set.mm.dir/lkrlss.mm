include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cbs.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "cplusg.mm"
include "wral.mm"
include "csca.mm"
include "c0g.mm"
include "wceq.mm"
include "crab.mm"
include "eqid.mm"
include "lkrval2.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "lmod0vcl.mm"
include "adantr.mm"
include "lfl0.mm"
include "ellkr.mm"
include "mpbir2and.mm"
include "ne0i.mm"
include "syl.mm"
include "simplll.mm"
include "simplr.mm"
include "simpllr.mm"
include "simprl.mm"
include "lkrcl.mm"
include "syl3anc.mm"
include "lmodvscl.mm"
include "simprr.mm"
include "lmodvacl.mm"
include "cmulr.mm"
include "lfli.mm"
include "syl113anc.mm"
include "lkrf0.mm"
include "oveq2d.mm"
include "crg.mm"
include "lmodring.mm"
include "ringrz.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "grpidcl.mm"
include "grplid.mm"
include "3eqtrd.mm"
include "wb.mm"
include "ad2antrr.mm"
include "ralrimivva.mm"
include "ralrimiva.mm"
include "islss.mm"
include "syl3anbrc.mm"

theorem lkrlss
  let cS: class S
  let cF: class F
  let cG: class G
  let cK: class K
  let cW: class W
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume lkrlss.f: |- F = ( LFnl ` W )
  assume lkrlss.k: |- K = ( LKer ` W )
  assume lkrlss.s: |- S = ( LSubSp ` W )


  assert |- ( ( W e. LMod /\ G e. F ) -> ( K ` G ) e. S )

  proof
    cW
    clmod
    wcel
    #
    cG
    cF
    wcel
    #
    wa
    #
    cG
    cK
    cfv
    #
    cW
    cbs
    cfv
    #
    wss
    @3
    c0
    wne
    #
    vr
    cv
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
    vy
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
    vy
    @3
    wral
    vx
    @3
    wral
    #
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
    cS
    wcel
    @2
    @3
    @7
    cG
    cfv
    #
    @15
    c0g
    cfv
    #
    wceq
    #
    vx
    @4
    crab
    @4
    vx
    @15
    cF
    cG
    cK
    @4
    cW
    clmod
    @18
    @4
    eqid
    #
    @15
    eqid
    #
    @18
    eqid
    #
    lkrlss.f
    lkrlss.k
    lkrval2
    @19
    vx
    @4
    ssrab2
    syl6eqss
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
    @24
    @23
    @4
    wcel
    #
    @23
    cG
    cfv
    @18
    wceq
    @0
    @25
    @1
    @4
    cW
    @23
    @20
    @23
    eqid
    #
    lmod0vcl
    adantr
    @15
    cF
    cG
    cW
    @18
    @23
    @21
    @22
    @26
    lkrlss.f
    lfl0
    @15
    cF
    cG
    cK
    @4
    cW
    @23
    clmod
    @18
    @20
    @21
    @22
    lkrlss.f
    lkrlss.k
    ellkr
    mpbir2and
    @3
    @23
    ne0i
    syl
    @2
    @14
    vr
    @16
    @2
    @6
    @16
    wcel
    #
    wa
    #
    @13
    vx
    vy
    @3
    @3
    @28
    @7
    @3
    wcel
    #
    @10
    @3
    wcel
    #
    wa
    #
    wa
    #
    @13
    @12
    @4
    wcel
    #
    @12
    cG
    cfv
    #
    @18
    wceq
    #
    @32
    @0
    @9
    @4
    wcel
    #
    @10
    @4
    wcel
    #
    @33
    @0
    @1
    @27
    @31
    simplll
    #
    @32
    @0
    @27
    @7
    @4
    wcel
    #
    @36
    @38
    @2
    @27
    @31
    simplr
    #
    @32
    @0
    @1
    @29
    @39
    @38
    @0
    @1
    @27
    @31
    simpllr
    #
    @28
    @29
    @30
    simprl
    #
    cF
    cG
    cK
    @4
    cW
    @7
    clmod
    @20
    lkrlss.f
    lkrlss.k
    lkrcl
    syl3anc
    #
    @6
    @8
    @15
    @16
    @4
    cW
    @7
    @20
    @21
    @8
    eqid
    #
    @16
    eqid
    #
    lmodvscl
    syl3anc
    @32
    @0
    @1
    @30
    @37
    @38
    @41
    @28
    @29
    @30
    simprr
    #
    cF
    cG
    cK
    @4
    cW
    @10
    clmod
    @20
    lkrlss.f
    lkrlss.k
    lkrcl
    syl3anc
    #
    @11
    @4
    cW
    @9
    @10
    @20
    @11
    eqid
    #
    lmodvacl
    syl3anc
    @32
    @34
    @6
    @17
    @15
    cmulr
    cfv
    #
    co
    #
    @10
    cG
    cfv
    #
    @15
    cplusg
    cfv
    #
    co
    #
    @18
    @18
    @52
    co
    #
    @18
    @32
    @0
    @1
    @27
    @39
    @37
    @34
    @53
    wceq
    @38
    @41
    @40
    @43
    @47
    @15
    @11
    @52
    @6
    @8
    @49
    cF
    cG
    @16
    @4
    cW
    @7
    @10
    clmod
    @20
    @48
    @21
    @44
    @45
    @52
    eqid
    #
    @49
    eqid
    #
    lkrlss.f
    lfli
    syl113anc
    @32
    @50
    @18
    @51
    @18
    @52
    @32
    @50
    @6
    @18
    @49
    co
    #
    @18
    @32
    @17
    @18
    @6
    @49
    @32
    @0
    @1
    @29
    @19
    @38
    @41
    @42
    @15
    cF
    cG
    cK
    cW
    @7
    clmod
    @18
    @21
    @22
    lkrlss.f
    lkrlss.k
    lkrf0
    syl3anc
    oveq2d
    @32
    @15
    crg
    wcel
    #
    @27
    @57
    @18
    wceq
    @32
    @0
    @58
    @38
    @15
    cW
    @21
    lmodring
    syl
    @40
    @16
    @15
    @49
    @6
    @18
    @45
    @56
    @22
    ringrz
    syl2anc
    eqtrd
    @32
    @0
    @1
    @30
    @51
    @18
    wceq
    @38
    @41
    @46
    @15
    cF
    cG
    cK
    cW
    @10
    clmod
    @18
    @21
    @22
    lkrlss.f
    lkrlss.k
    lkrf0
    syl3anc
    oveq12d
    @32
    @15
    cgrp
    wcel
    #
    @18
    @16
    wcel
    #
    @54
    @18
    wceq
    @32
    @0
    @59
    @38
    @15
    cW
    @21
    lmodfgrp
    syl
    #
    @32
    @59
    @60
    @61
    @16
    @15
    @18
    @45
    @22
    grpidcl
    syl
    @16
    @52
    @15
    @18
    @18
    @45
    @55
    @22
    grplid
    syl2anc
    3eqtrd
    @2
    @13
    @33
    @35
    wa
    wb
    @27
    @31
    @15
    cF
    cG
    cK
    @4
    cW
    @12
    clmod
    @18
    @20
    @21
    @22
    lkrlss.f
    lkrlss.k
    ellkr
    ad2antrr
    mpbir2and
    ralrimivva
    ralrimiva
    vr
    @16
    @11
    cS
    @8
    @3
    @15
    @4
    cW
    vx
    vy
    @21
    @45
    @20
    @48
    @44
    lkrlss.s
    islss
    syl3anbrc
end
