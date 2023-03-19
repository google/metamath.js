include "wcel.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "sseld.mm"
include "clmod.mm"
include "wb.mm"
include "cphl.mm"
include "phllmod.mm"
include "syl.mm"
include "ocvss.mm"
include "a1i.mm"
include "eqid.mm"
include "lsmelvalx.mm"
include "syl3anc.mm"
include "sylibd.mm"
include "wa.mm"
include "c0g.mm"
include "cip.mm"
include "csca.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "sseldd.mm"
include "simplrr.mm"
include "sseldi.mm"
include "ipdir.mm"
include "syl13anc.mm"
include "ocvi.mm"
include "syl2anc.mm"
include "iporthcom.mm"
include "mpbid.mm"
include "oveq1d.mm"
include "cgrp.mm"
include "cbs.mm"
include "lmodfgrp.mm"
include "ipcl.mm"
include "grplid.mm"
include "3eqtrd.mm"
include "simpr.mm"
include "eqtr3d.mm"
include "ipeq0.mm"
include "oveq2d.mm"
include "lmodgrp.mm"
include "grprid.mm"
include "eqtrd.mm"
include "eqeltrd.mm"
include "ex.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "syld.mm"
include "pm2.43d.mm"
include "ssrdv.mm"
include "iscss2.mm"
include "mpbird.mm"

theorem lsmcss
  let wph: wff ph
  let cC: class C
  let c.po: class .(+)
  let cS: class S
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lsmcss.c: |- C = ( CSubSp ` W )
  assume lsmcss.j: |- V = ( Base ` W )
  assume lsmcss.o: |- ._|_ = ( ocv ` W )
  assume lsmcss.p: |- .(+) = ( LSSum ` W )
  assume lsmcss.1: |- ( ph -> W e. PreHil )
  assume lsmcss.2: |- ( ph -> S C_ V )
  assume lsmcss.3: |- ( ph -> ( ._|_ ` ( ._|_ ` S ) ) C_ ( S .(+) ( ._|_ ` S ) ) )


  assert |- ( ph -> S e. C )

  proof
    wph
    cS
    cC
    wcel
    #
    cS
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cS
    wss
    #
    wph
    vx
    @2
    cS
    wph
    vx
    cv
    #
    @2
    wcel
    #
    @4
    cS
    wcel
    #
    wph
    @5
    @4
    vy
    cv
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
    wceq
    #
    vz
    @1
    wrex
    vy
    cS
    wrex
    #
    @5
    @6
    wi
    #
    wph
    @5
    @4
    cS
    @1
    c.po
    co
    #
    wcel
    #
    @12
    wph
    @2
    @14
    @4
    lsmcss.3
    sseld
    wph
    cW
    clmod
    wcel
    #
    cS
    cV
    wss
    #
    @1
    cV
    wss
    #
    @15
    @12
    wb
    wph
    cW
    cphl
    wcel
    #
    @16
    lsmcss.1
    cW
    phllmod
    #
    syl
    #
    lsmcss.2
    @18
    wph
    cS
    c.pe
    cV
    cW
    lsmcss.j
    lsmcss.o
    ocvss
    #
    a1i
    vy
    vz
    cV
    @9
    c.po
    cS
    @1
    cW
    clmod
    @4
    lsmcss.j
    @9
    eqid
    #
    lsmcss.p
    lsmelvalx
    syl3anc
    sylibd
    wph
    @11
    @13
    vy
    vz
    cS
    @1
    wph
    @7
    cS
    wcel
    #
    @8
    @1
    wcel
    #
    wa
    #
    wa
    #
    @13
    @11
    @10
    @2
    wcel
    #
    @10
    cS
    wcel
    #
    wi
    @27
    @28
    @29
    @27
    @28
    wa
    #
    @10
    @7
    cS
    @30
    @10
    @7
    cW
    c0g
    cfv
    #
    @9
    co
    #
    @7
    @30
    @8
    @31
    @7
    @9
    @30
    @8
    @8
    cW
    cip
    cfv
    #
    co
    #
    cW
    csca
    cfv
    #
    c0g
    cfv
    #
    wceq
    #
    @8
    @31
    wceq
    #
    @30
    @10
    @8
    @33
    co
    #
    @34
    @36
    @30
    @39
    @7
    @8
    @33
    co
    #
    @34
    @35
    cplusg
    cfv
    #
    co
    #
    @36
    @34
    @41
    co
    #
    @34
    @30
    @19
    @7
    cV
    wcel
    #
    @8
    cV
    wcel
    #
    @45
    @39
    @42
    wceq
    wph
    @19
    @26
    @28
    lsmcss.1
    ad2antrr
    #
    @30
    cS
    cV
    @7
    wph
    @17
    @26
    @28
    lsmcss.2
    ad2antrr
    wph
    @24
    @25
    @28
    simplrl
    #
    sseldd
    #
    @30
    @1
    cV
    @8
    @22
    wph
    @24
    @25
    @28
    simplrr
    #
    sseldi
    #
    @50
    @7
    @8
    @8
    @9
    @41
    @35
    @33
    cV
    cW
    @35
    eqid
    #
    @33
    eqid
    #
    lsmcss.j
    @23
    @41
    eqid
    #
    ipdir
    syl13anc
    @30
    @40
    @36
    @34
    @41
    @30
    @8
    @7
    @33
    co
    @36
    wceq
    #
    @40
    @36
    wceq
    #
    @30
    @25
    @24
    @54
    @49
    @47
    @8
    @7
    cS
    @35
    @33
    c.pe
    cV
    cW
    @36
    lsmcss.j
    @52
    @51
    @36
    eqid
    #
    lsmcss.o
    ocvi
    syl2anc
    @30
    @19
    @45
    @44
    @54
    @55
    wb
    @46
    @50
    @48
    @8
    @7
    @35
    @33
    cV
    cW
    @36
    @51
    @52
    lsmcss.j
    @56
    iporthcom
    syl3anc
    mpbid
    oveq1d
    @30
    @35
    cgrp
    wcel
    #
    @34
    @35
    cbs
    cfv
    #
    wcel
    #
    @43
    @34
    wceq
    @30
    @16
    @57
    @30
    @19
    @16
    @46
    @20
    syl
    @35
    cW
    @51
    lmodfgrp
    syl
    @30
    @19
    @45
    @45
    @59
    @46
    @50
    @50
    @8
    @8
    @35
    @33
    @58
    cV
    cW
    @51
    @52
    lsmcss.j
    @58
    eqid
    #
    ipcl
    syl3anc
    @58
    @41
    @35
    @34
    @36
    @60
    @53
    @56
    grplid
    syl2anc
    3eqtrd
    @30
    @28
    @25
    @39
    @36
    wceq
    @27
    @28
    simpr
    @49
    @10
    @8
    @1
    @35
    @33
    c.pe
    cV
    cW
    @36
    lsmcss.j
    @52
    @51
    @56
    lsmcss.o
    ocvi
    syl2anc
    eqtr3d
    @30
    @19
    @45
    @37
    @38
    wb
    @46
    @50
    @8
    @35
    @33
    cV
    cW
    @31
    @36
    @51
    @52
    lsmcss.j
    @56
    @31
    eqid
    #
    ipeq0
    syl2anc
    mpbid
    oveq2d
    @30
    cW
    cgrp
    wcel
    #
    @44
    @32
    @7
    wceq
    wph
    @62
    @26
    @28
    wph
    @16
    @62
    @21
    cW
    lmodgrp
    syl
    ad2antrr
    @48
    cV
    @9
    cW
    @7
    @31
    lsmcss.j
    @23
    @61
    grprid
    syl2anc
    eqtrd
    @47
    eqeltrd
    ex
    @11
    @5
    @28
    @6
    @29
    @4
    @10
    @2
    eleq1
    @4
    @10
    cS
    eleq1
    imbi12d
    syl5ibrcom
    rexlimdvva
    syld
    pm2.43d
    ssrdv
    wph
    @19
    @17
    @0
    @3
    wb
    lsmcss.1
    lsmcss.2
    cC
    cS
    c.pe
    cV
    cW
    lsmcss.j
    lsmcss.c
    lsmcss.o
    iscss2
    syl2anc
    mpbird
end
