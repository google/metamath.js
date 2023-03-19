include "co.mm"
include "wcel.mm"
include "wss.mm"
include "clmod.mm"
include "clmhm.mm"
include "lmhmlmod1.mm"
include "syl.mm"
include "lmhmkerlss.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "lssss.mm"
include "cv.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "cima.mm"
include "crn.mm"
include "wfn.mm"
include "cbs.mm"
include "wf.mm"
include "eqid.mm"
include "lmhmf.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "wb.mm"
include "fvelimab.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "wi.mm"
include "csg.mm"
include "cplusg.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "simprl.mm"
include "sselda.mm"
include "adantrl.mm"
include "grpnpcan.mm"
include "ad2antrr.mm"
include "eqcom.mm"
include "cghm.mm"
include "lmghm.mm"
include "ghmeqker.mm"
include "syl5bb.mm"
include "biimpa.mm"
include "simplrr.mm"
include "lsmelvalix.mm"
include "syl32anc.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "anassrs.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem kercvrlsm
  let wph: wff ph
  let cB: class B
  let cD: class D
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cK: class K
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  assume kercvrlsm.u: |- U = ( LSubSp ` S )
  assume kercvrlsm.p: |- .(+) = ( LSSum ` S )
  assume kercvrlsm.z: |- .0. = ( 0g ` T )
  assume kercvrlsm.k: |- K = ( `' F " { .0. } )
  assume kercvrlsm.b: |- B = ( Base ` S )
  assume kercvrlsm.f: |- ( ph -> F e. ( S LMHom T ) )
  assume kercvrlsm.d: |- ( ph -> D e. U )
  assume kercvrlsm.cv: |- ( ph -> ( F " D ) = ran F )


  assert |- ( ph -> ( K .(+) D ) = B )

  proof
    wph
    cK
    cD
    c.po
    co
    #
    cB
    wph
    @0
    cU
    wcel
    #
    @0
    cB
    wss
    wph
    cS
    clmod
    wcel
    #
    cK
    cU
    wcel
    #
    cD
    cU
    wcel
    #
    @1
    wph
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    @2
    kercvrlsm.f
    cS
    cT
    cF
    lmhmlmod1
    syl
    #
    wph
    @5
    @3
    kercvrlsm.f
    cS
    cT
    cU
    cF
    cK
    c.0
    kercvrlsm.k
    kercvrlsm.z
    kercvrlsm.u
    lmhmkerlss
    syl
    #
    kercvrlsm.d
    c.po
    cU
    cK
    cD
    cS
    kercvrlsm.u
    kercvrlsm.p
    lsmcl
    syl3anc
    cU
    @0
    cB
    cS
    kercvrlsm.b
    kercvrlsm.u
    lssss
    syl
    wph
    va
    cB
    @0
    wph
    va
    cv
    #
    cB
    wcel
    #
    @8
    @0
    wcel
    #
    wph
    @9
    wa
    #
    vb
    cv
    #
    cF
    cfv
    #
    @8
    cF
    cfv
    #
    wceq
    #
    vb
    cD
    wrex
    #
    @10
    @11
    @14
    cF
    cD
    cima
    #
    wcel
    #
    @16
    @11
    @14
    cF
    crn
    #
    @17
    wph
    cF
    cB
    wfn
    #
    @9
    @14
    @19
    wcel
    wph
    cB
    cT
    cbs
    cfv
    #
    cF
    wf
    #
    @20
    wph
    @5
    @22
    kercvrlsm.f
    cB
    @21
    cS
    cT
    cF
    kercvrlsm.b
    @21
    eqid
    lmhmf
    syl
    cB
    @21
    cF
    ffn
    syl
    #
    cB
    @8
    cF
    fnfvelrn
    sylan
    wph
    @17
    @19
    wceq
    @9
    kercvrlsm.cv
    adantr
    eleqtrrd
    @11
    @20
    cD
    cB
    wss
    #
    @18
    @16
    wb
    wph
    @20
    @9
    @23
    adantr
    wph
    @24
    @9
    wph
    @4
    @24
    kercvrlsm.d
    cU
    cD
    cB
    cS
    kercvrlsm.b
    kercvrlsm.u
    lssss
    syl
    #
    adantr
    vb
    cB
    cD
    @14
    cF
    fvelimab
    syl2anc
    mpbid
    @11
    @15
    @10
    vb
    cD
    wph
    @9
    @12
    cD
    wcel
    #
    @15
    @10
    wi
    wph
    @9
    @26
    wa
    #
    wa
    #
    @15
    @10
    @28
    @15
    wa
    #
    @8
    @12
    cS
    csg
    cfv
    #
    co
    #
    @12
    cS
    cplusg
    cfv
    #
    co
    #
    @8
    @0
    @28
    @33
    @8
    wceq
    #
    @15
    @28
    cS
    cgrp
    wcel
    #
    @9
    @12
    cB
    wcel
    #
    @34
    wph
    @35
    @27
    wph
    @2
    @35
    @6
    cS
    lmodgrp
    syl
    adantr
    wph
    @9
    @26
    simprl
    #
    wph
    @26
    @36
    @9
    wph
    cD
    cB
    @12
    @25
    sselda
    adantrl
    #
    cB
    @32
    cS
    @30
    @8
    @12
    kercvrlsm.b
    @32
    eqid
    #
    @30
    eqid
    #
    grpnpcan
    syl3anc
    adantr
    @29
    @2
    cK
    cB
    wss
    #
    @24
    @31
    cK
    wcel
    #
    @26
    @33
    @0
    wcel
    wph
    @2
    @27
    @15
    @6
    ad2antrr
    wph
    @41
    @27
    @15
    wph
    @3
    @41
    @7
    cU
    cK
    cB
    cS
    kercvrlsm.b
    kercvrlsm.u
    lssss
    syl
    ad2antrr
    wph
    @24
    @27
    @15
    @25
    ad2antrr
    @28
    @15
    @42
    @15
    @14
    @13
    wceq
    #
    @28
    @42
    @13
    @14
    eqcom
    @28
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    @9
    @36
    @43
    @42
    wb
    wph
    @44
    @27
    wph
    @5
    @44
    kercvrlsm.f
    cS
    cT
    cF
    lmghm
    syl
    adantr
    @37
    @38
    cB
    cS
    cT
    @8
    cF
    cK
    @30
    @12
    c.0
    kercvrlsm.b
    kercvrlsm.z
    kercvrlsm.k
    @40
    ghmeqker
    syl3anc
    syl5bb
    biimpa
    wph
    @9
    @26
    @15
    simplrr
    cB
    @32
    c.po
    cK
    cD
    cS
    clmod
    @31
    @12
    kercvrlsm.b
    @39
    kercvrlsm.p
    lsmelvalix
    syl32anc
    eqeltrrd
    ex
    anassrs
    rexlimdva
    mpd
    ex
    ssrdv
    eqssd
end
