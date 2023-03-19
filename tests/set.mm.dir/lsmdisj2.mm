include "co.mm"
include "cin.mm"
include "csn.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cplusg.mm"
include "cfv.mm"
include "wrex.mm"
include "wi.mm"
include "csubg.mm"
include "wb.mm"
include "eqid.mm"
include "lsmelval.mm"
include "syl2anc.mm"
include "simplrl.mm"
include "cminusg.mm"
include "cgrp.mm"
include "cbs.mm"
include "subgrcl.mm"
include "syl.mm"
include "ad2antrr.mm"
include "wss.mm"
include "subgss.mm"
include "sseldd.mm"
include "grplinv.mm"
include "oveq1d.mm"
include "subginvcl.mm"
include "simplrr.mm"
include "grpass.mm"
include "syl13anc.mm"
include "grplid.mm"
include "3eqtr3d.mm"
include "simpr.mm"
include "lsmelvali.mm"
include "syl22anc.mm"
include "eqeltrrd.mm"
include "elind.mm"
include "eleqtrd.mm"
include "elsni.mm"
include "oveq2d.mm"
include "grprid.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "grpidcl.mm"
include "ex.mm"
include "eleq1.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "sylbid.mm"
include "com23.mm"
include "impd.mm"
include "elin.mm"
include "velsn.mm"
include "3imtr4g.mm"
include "ssrdv.mm"
include "subg0cl.mm"
include "lsmub1.mm"
include "snssd.mm"
include "eqssd.mm"

theorem lsmdisj2
  let wph: wff ph
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cU: class U
  let cG: class G
  let c.0: class .0.
  let vx: setvar x
  let vs: setvar s
  let vu: setvar u
  assume lsmcntz.p: |- .(+) = ( LSSum ` G )
  assume lsmcntz.s: |- ( ph -> S e. ( SubGrp ` G ) )
  assume lsmcntz.t: |- ( ph -> T e. ( SubGrp ` G ) )
  assume lsmcntz.u: |- ( ph -> U e. ( SubGrp ` G ) )
  assume lsmdisj.o: |- .0. = ( 0g ` G )
  assume lsmdisj.i: |- ( ph -> ( ( S .(+) T ) i^i U ) = { .0. } )
  assume lsmdisj2.i: |- ( ph -> ( S i^i T ) = { .0. } )


  assert |- ( ph -> ( T i^i ( S .(+) U ) ) = { .0. } )

  proof
    wph
    cT
    cS
    cU
    c.po
    co
    #
    cin
    #
    c.0
    csn
    #
    wph
    vx
    @1
    @2
    wph
    vx
    cv
    #
    cT
    wcel
    #
    @3
    @0
    wcel
    #
    wa
    @3
    c.0
    wceq
    #
    @3
    @1
    wcel
    @3
    @2
    wcel
    wph
    @4
    @5
    @6
    wph
    @5
    @4
    @6
    wph
    @5
    @3
    vs
    cv
    #
    vu
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
    vu
    cU
    wrex
    vs
    cS
    wrex
    #
    @4
    @6
    wi
    #
    wph
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    cU
    @14
    wcel
    #
    @5
    @12
    wb
    lsmcntz.s
    lsmcntz.u
    vs
    vu
    @9
    c.po
    cS
    cU
    cG
    @3
    @9
    eqid
    #
    lsmcntz.p
    lsmelval
    syl2anc
    wph
    @11
    @13
    vs
    vu
    cS
    cU
    wph
    @7
    cS
    wcel
    #
    @8
    cU
    wcel
    #
    wa
    #
    wa
    #
    @13
    @11
    @10
    cT
    wcel
    #
    @10
    c.0
    wceq
    #
    wi
    @21
    @22
    @23
    @21
    @22
    wa
    #
    @10
    c.0
    c.0
    @9
    co
    #
    c.0
    @24
    @7
    c.0
    @8
    c.0
    @9
    @24
    @7
    @2
    wcel
    @7
    c.0
    wceq
    @24
    @7
    cS
    cT
    cin
    #
    @2
    @24
    cS
    cT
    @7
    wph
    @18
    @19
    @22
    simplrl
    #
    @24
    @10
    @7
    cT
    @24
    @10
    @7
    c.0
    @9
    co
    #
    @7
    @24
    @8
    c.0
    @7
    @9
    @24
    @8
    @2
    wcel
    @8
    c.0
    wceq
    @24
    @8
    cS
    cT
    c.po
    co
    #
    cU
    cin
    #
    @2
    @24
    @29
    cU
    @8
    @24
    @7
    cG
    cminusg
    cfv
    #
    cfv
    #
    @10
    @9
    co
    #
    @8
    @29
    @24
    @32
    @7
    @9
    co
    #
    @8
    @9
    co
    #
    c.0
    @8
    @9
    co
    #
    @33
    @8
    @24
    @34
    c.0
    @8
    @9
    @24
    cG
    cgrp
    wcel
    #
    @7
    cG
    cbs
    cfv
    #
    wcel
    #
    @34
    c.0
    wceq
    wph
    @37
    @20
    @22
    wph
    @15
    @37
    lsmcntz.s
    cS
    cG
    subgrcl
    syl
    #
    ad2antrr
    #
    @24
    cS
    @38
    @7
    @24
    @15
    cS
    @38
    wss
    wph
    @15
    @20
    @22
    lsmcntz.s
    ad2antrr
    #
    @38
    cS
    cG
    @38
    eqid
    #
    subgss
    syl
    #
    @27
    sseldd
    #
    @38
    @9
    cG
    @31
    @7
    c.0
    @43
    @17
    lsmdisj.o
    @31
    eqid
    #
    grplinv
    syl2anc
    oveq1d
    @24
    @37
    @32
    @38
    wcel
    @39
    @8
    @38
    wcel
    #
    @35
    @33
    wceq
    @41
    @24
    cS
    @38
    @32
    @44
    @24
    @15
    @18
    @32
    cS
    wcel
    #
    @42
    @27
    cS
    cG
    @31
    @7
    @46
    subginvcl
    syl2anc
    #
    sseldd
    @45
    @24
    cU
    @38
    @8
    @24
    @16
    cU
    @38
    wss
    wph
    @16
    @20
    @22
    lsmcntz.u
    ad2antrr
    @38
    cU
    cG
    @43
    subgss
    syl
    wph
    @18
    @19
    @22
    simplrr
    #
    sseldd
    #
    @38
    @9
    cG
    @32
    @7
    @8
    @43
    @17
    grpass
    syl13anc
    @24
    @37
    @47
    @36
    @8
    wceq
    @41
    @51
    @38
    @9
    cG
    @8
    c.0
    @43
    @17
    lsmdisj.o
    grplid
    syl2anc
    3eqtr3d
    @24
    @15
    cT
    @14
    wcel
    #
    @48
    @22
    @33
    @29
    wcel
    @42
    wph
    @52
    @20
    @22
    lsmcntz.t
    ad2antrr
    @49
    @21
    @22
    simpr
    #
    @9
    c.po
    cS
    cT
    cG
    @32
    @10
    @17
    lsmcntz.p
    lsmelvali
    syl22anc
    eqeltrrd
    @50
    elind
    wph
    @30
    @2
    wceq
    @20
    @22
    lsmdisj.i
    ad2antrr
    eleqtrd
    @8
    c.0
    elsni
    syl
    #
    oveq2d
    @24
    @37
    @39
    @28
    @7
    wceq
    @41
    @45
    @38
    @9
    cG
    @7
    c.0
    @43
    @17
    lsmdisj.o
    grprid
    syl2anc
    eqtrd
    @53
    eqeltrrd
    elind
    wph
    @26
    @2
    wceq
    @20
    @22
    lsmdisj2.i
    ad2antrr
    eleqtrd
    @7
    c.0
    elsni
    syl
    @54
    oveq12d
    wph
    @25
    c.0
    wceq
    #
    @20
    @22
    wph
    @37
    c.0
    @38
    wcel
    #
    @55
    @40
    wph
    @37
    @56
    @40
    @38
    cG
    c.0
    @43
    lsmdisj.o
    grpidcl
    syl
    @38
    @9
    cG
    c.0
    c.0
    @43
    @17
    lsmdisj.o
    grplid
    syl2anc
    ad2antrr
    eqtrd
    ex
    @11
    @4
    @22
    @6
    @23
    @3
    @10
    cT
    eleq1
    @3
    @10
    c.0
    eqeq1
    imbi12d
    syl5ibrcom
    rexlimdvva
    sylbid
    com23
    impd
    @3
    cT
    @0
    elin
    vx
    c.0
    velsn
    3imtr4g
    ssrdv
    wph
    c.0
    @1
    wph
    cT
    @0
    c.0
    wph
    @52
    c.0
    cT
    wcel
    lsmcntz.t
    cT
    cG
    c.0
    lsmdisj.o
    subg0cl
    syl
    wph
    cS
    @0
    c.0
    wph
    @15
    @16
    cS
    @0
    wss
    lsmcntz.s
    lsmcntz.u
    c.po
    cS
    cU
    cG
    lsmcntz.p
    lsmub1
    syl2anc
    wph
    @15
    c.0
    cS
    wcel
    lsmcntz.s
    cS
    cG
    c.0
    lsmdisj.o
    subg0cl
    syl
    sseldd
    elind
    snssd
    eqssd
end
