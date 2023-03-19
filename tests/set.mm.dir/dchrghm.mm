include "cres.mm"
include "cmhm.mm"
include "co.mm"
include "cghm.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "cfv.mm"
include "wcel.mm"
include "csubmnd.mm"
include "dchrmhm.mm"
include "sseldi.mm"
include "crg.mm"
include "ccrg.mm"
include "cn0.mm"
include "cn.mm"
include "dchrrcl.mm"
include "syl.mm"
include "nnnn0d.mm"
include "zncrng.mm"
include "crngring.mm"
include "eqid.mm"
include "unitsubm.mm"
include "resmhm.mm"
include "syl2anc.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "crn.mm"
include "wss.mm"
include "wb.mm"
include "cnring.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "cndrng.mm"
include "drngui.mm"
include "ax-mp.mm"
include "cima.mm"
include "df-ima.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "wne.mm"
include "cbs.mm"
include "wf.mm"
include "dchrf.mm"
include "unitss.mm"
include "sseli.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "simpr.mm"
include "adantr.mm"
include "adantl.mm"
include "dchrn0.mm"
include "mpbird.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "ralrimiva.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "wceq.mm"
include "fdm.mm"
include "syl5sseqr.mm"
include "funimass4.mm"
include "syl5eqssr.mm"
include "resmhm2b.mm"
include "sylancr.mm"
include "mpbid.mm"
include "cgrp.mm"
include "unitgrp.mm"
include "cabl.mm"
include "cnmgpabl.mm"
include "ablgrp.mm"
include "ghmmhmb.mm"
include "sylancl.mm"
include "eleqtrrd.mm"

theorem dchrghm
  let wph: wff ph
  let cD: class D
  let cU: class U
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vx: setvar x
  assume dchrghm.g: |- G = ( DChr ` N )
  assume dchrghm.z: |- Z = ( Z/nZ ` N )
  assume dchrghm.b: |- D = ( Base ` G )
  assume dchrghm.u: |- U = ( Unit ` Z )
  assume dchrghm.h: |- H = ( ( mulGrp ` Z ) |`s U )
  assume dchrghm.m: |- M = ( ( mulGrp ` CCfld ) |`s ( CC \ { 0 } ) )
  assume dchrghm.x: |- ( ph -> X e. D )


  assert |- ( ph -> ( X |` U ) e. ( H GrpHom M ) )

  proof
    wph
    cX
    cU
    cres
    #
    cH
    cM
    cmhm
    co
    #
    cH
    cM
    cghm
    co
    #
    wph
    @0
    cH
    ccnfld
    cmgp
    cfv
    #
    cmhm
    co
    wcel
    #
    @0
    @1
    wcel
    #
    wph
    cX
    cZ
    cmgp
    cfv
    #
    @3
    cmhm
    co
    #
    wcel
    cU
    @6
    csubmnd
    cfv
    wcel
    #
    @4
    wph
    cD
    @7
    cX
    cD
    cG
    cN
    cZ
    dchrghm.g
    dchrghm.z
    dchrghm.b
    dchrmhm
    dchrghm.x
    sseldi
    wph
    cZ
    crg
    wcel
    #
    @8
    wph
    cZ
    ccrg
    wcel
    #
    @9
    wph
    cN
    cn0
    wcel
    @10
    wph
    cN
    wph
    cX
    cD
    wcel
    #
    cN
    cn
    wcel
    dchrghm.x
    cD
    cG
    cN
    cX
    dchrghm.g
    dchrghm.b
    dchrrcl
    syl
    nnnn0d
    cN
    cZ
    dchrghm.z
    zncrng
    syl
    cZ
    crngring
    syl
    #
    cZ
    cU
    @6
    dchrghm.u
    @6
    eqid
    unitsubm
    syl
    @6
    @3
    cH
    cX
    cU
    dchrghm.h
    resmhm
    syl2anc
    wph
    cc
    cc0
    csn
    cdif
    #
    @3
    csubmnd
    cfv
    wcel
    #
    @0
    crn
    #
    @13
    wss
    @4
    @5
    wb
    ccnfld
    crg
    wcel
    @14
    cnring
    ccnfld
    @13
    @3
    cc
    ccnfld
    cc0
    cnfldbas
    cnfld0
    cndrng
    drngui
    @3
    eqid
    unitsubm
    ax-mp
    wph
    @15
    cX
    cU
    cima
    #
    @13
    cX
    cU
    df-ima
    wph
    @16
    @13
    wss
    #
    vx
    cv
    #
    cX
    cfv
    #
    @13
    wcel
    #
    vx
    cU
    wral
    #
    wph
    @20
    vx
    cU
    wph
    @18
    cU
    wcel
    #
    wa
    #
    @19
    cc
    wcel
    #
    @19
    cc0
    wne
    #
    @20
    wph
    cZ
    cbs
    cfv
    #
    cc
    cX
    wf
    #
    @18
    @26
    wcel
    #
    @24
    @22
    wph
    @26
    cD
    cG
    cN
    cX
    cZ
    dchrghm.g
    dchrghm.z
    dchrghm.b
    @26
    eqid
    #
    dchrghm.x
    dchrf
    #
    cU
    @26
    @18
    @26
    cZ
    cU
    @29
    dchrghm.u
    unitss
    #
    sseli
    #
    @26
    cc
    @18
    cX
    ffvelrn
    syl2an
    @23
    @25
    @22
    wph
    @22
    simpr
    @23
    @18
    @26
    cD
    cU
    cG
    cN
    cX
    cZ
    dchrghm.g
    dchrghm.z
    dchrghm.b
    @29
    dchrghm.u
    wph
    @11
    @22
    dchrghm.x
    adantr
    @22
    @28
    wph
    @32
    adantl
    dchrn0
    mpbird
    @19
    cc
    cc0
    eldifsn
    sylanbrc
    ralrimiva
    wph
    cX
    wfun
    #
    cU
    cX
    cdm
    #
    wss
    @17
    @21
    wb
    wph
    @27
    @33
    @30
    @26
    cc
    cX
    ffun
    syl
    wph
    @26
    cU
    @34
    @31
    wph
    @27
    @34
    @26
    wceq
    @30
    @26
    cc
    cX
    fdm
    syl
    syl5sseqr
    vx
    cU
    @13
    cX
    funimass4
    syl2anc
    mpbird
    syl5eqssr
    cH
    @3
    cM
    @0
    @13
    dchrghm.m
    resmhm2b
    sylancr
    mpbid
    wph
    cH
    cgrp
    wcel
    #
    cM
    cgrp
    wcel
    #
    @2
    @1
    wceq
    wph
    @9
    @35
    @12
    cZ
    cU
    cH
    dchrghm.u
    dchrghm.h
    unitgrp
    syl
    cM
    cabl
    wcel
    @36
    cM
    dchrghm.m
    cnmgpabl
    cM
    ablgrp
    ax-mp
    cH
    cM
    ghmmhmb
    sylancl
    eleqtrrd
end
