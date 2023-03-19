include "ccom.mm"
include "climc.mm"
include "co.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "cdm.mm"
include "csn.mm"
include "cdif.mm"
include "cin.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "limccl.mm"
include "sseldi.mm"
include "wf.mm"
include "w3a.mm"
include "limcrcl.mm"
include "syl.mm"
include "simp1d.mm"
include "simp2d.mm"
include "simp3d.mm"
include "eqid.mm"
include "ellimc2.mm"
include "mpbid.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "imp.mm"
include "simp1ll.mm"
include "simp2.mm"
include "simp3l.mm"
include "syl21anc.mm"
include "imaco.mm"
include "ad2antrr.mm"
include "simpl3r.mm"
include "adantr.mm"
include "simpr.mm"
include "crn.mm"
include "imassrn.mm"
include "syl5ss.mm"
include "ssind.mm"
include "imass2.mm"
include "adantlr.mm"
include "simplr.mm"
include "sstrd.mm"
include "syl5eqss.mm"
include "ex.mm"
include "anim2d.mm"
include "reximdva.mm"
include "mpd.mm"
include "rexlimdv3a.mm"
include "ralrimiva.mm"
include "wfun.mm"
include "ffun.mm"
include "fdmrn.mm"
include "sylib.mm"
include "difss2d.mm"
include "fssd.mm"
include "fco.mm"
include "syl2anc.mm"
include "mpbir2and.mm"

theorem limccog
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume limccog.1: |- ( ph -> ran F C_ ( dom G \ { B } ) )
  assume limccog.2: |- ( ph -> B e. ( F limCC A ) )
  assume limccog.3: |- ( ph -> C e. ( G limCC B ) )


  assert |- ( ph -> C e. ( ( G o. F ) limCC A ) )

  proof
    wph
    cC
    cG
    cF
    ccom
    #
    cA
    climc
    co
    wcel
    cC
    cc
    wcel
    #
    cC
    vu
    cv
    #
    wcel
    #
    cA
    vw
    cv
    #
    wcel
    #
    @0
    @4
    cF
    cdm
    #
    cA
    csn
    cdif
    cin
    #
    cima
    #
    @2
    wss
    #
    wa
    #
    vw
    ccnfld
    ctopn
    cfv
    #
    wrex
    #
    wi
    #
    vu
    @11
    wral
    wph
    cG
    cB
    climc
    co
    #
    cc
    cC
    cB
    cG
    limccl
    limccog.3
    sseldi
    wph
    @13
    vu
    @11
    wph
    @2
    @11
    wcel
    #
    wa
    #
    @3
    @12
    @16
    @3
    wa
    #
    cB
    vv
    cv
    #
    wcel
    #
    cG
    @18
    cG
    cdm
    #
    cB
    csn
    #
    cdif
    #
    cin
    #
    cima
    #
    @2
    wss
    #
    wa
    #
    vv
    @11
    wrex
    #
    @12
    @16
    @3
    @27
    wph
    @3
    @27
    wi
    #
    vu
    @11
    wph
    @1
    @28
    vu
    @11
    wral
    #
    wph
    cC
    @14
    wcel
    #
    @1
    @29
    wa
    limccog.3
    wph
    vv
    vu
    @20
    cB
    cC
    cG
    @11
    wph
    @20
    cc
    cG
    wf
    #
    @20
    cc
    wss
    #
    cB
    cc
    wcel
    #
    wph
    @30
    @31
    @32
    @33
    w3a
    limccog.3
    cB
    cC
    cG
    limcrcl
    syl
    #
    simp1d
    #
    wph
    @31
    @32
    @33
    @34
    simp2d
    wph
    @31
    @32
    @33
    @34
    simp3d
    @11
    eqid
    #
    ellimc2
    mpbid
    simprd
    r19.21bi
    imp
    @17
    @26
    @12
    vv
    @11
    @17
    @18
    @11
    wcel
    #
    @26
    w3a
    #
    @5
    cF
    @7
    cima
    #
    @18
    wss
    #
    wa
    #
    vw
    @11
    wrex
    #
    @12
    @38
    wph
    @37
    @19
    @42
    wph
    @15
    @3
    @37
    @26
    simp1ll
    #
    @17
    @37
    @26
    simp2
    @17
    @37
    @19
    @25
    simp3l
    wph
    @37
    wa
    @19
    @42
    wph
    @19
    @42
    wi
    #
    vv
    @11
    wph
    @33
    @44
    vv
    @11
    wral
    #
    wph
    cB
    cF
    cA
    climc
    co
    wcel
    #
    @33
    @45
    wa
    limccog.2
    wph
    vw
    vv
    @6
    cA
    cB
    cF
    @11
    wph
    @6
    cc
    cF
    wf
    #
    @6
    cc
    wss
    #
    cA
    cc
    wcel
    #
    wph
    @46
    @47
    @48
    @49
    w3a
    limccog.2
    cA
    cB
    cF
    limcrcl
    syl
    #
    simp1d
    #
    wph
    @47
    @48
    @49
    @50
    simp2d
    #
    wph
    @47
    @48
    @49
    @50
    simp3d
    #
    @36
    ellimc2
    mpbid
    simprd
    r19.21bi
    imp
    syl21anc
    @38
    @41
    @10
    vw
    @11
    @38
    @4
    @11
    wcel
    #
    wa
    #
    @40
    @9
    @5
    @55
    @40
    @9
    @55
    @40
    wa
    #
    @8
    cG
    @39
    cima
    #
    @2
    cG
    cF
    @7
    imaco
    @56
    wph
    @25
    @40
    @57
    @2
    wss
    @38
    wph
    @54
    @40
    @43
    ad2antrr
    @55
    @25
    @40
    @19
    @25
    @17
    @37
    @54
    simpl3r
    adantr
    @55
    @40
    simpr
    wph
    @25
    wa
    @40
    wa
    @57
    @24
    @2
    wph
    @40
    @57
    @24
    wss
    #
    @25
    wph
    @40
    wa
    #
    @39
    @23
    wss
    @58
    @59
    @39
    @18
    @22
    wph
    @40
    simpr
    wph
    @39
    @22
    wss
    @40
    wph
    @39
    cF
    crn
    #
    @22
    cF
    @7
    imassrn
    limccog.1
    syl5ss
    adantr
    ssind
    @39
    @23
    cG
    imass2
    syl
    adantlr
    wph
    @25
    @40
    simplr
    sstrd
    syl21anc
    syl5eqss
    ex
    anim2d
    reximdva
    mpd
    rexlimdv3a
    mpd
    ex
    ralrimiva
    wph
    vw
    vu
    @6
    cA
    cC
    @0
    @11
    wph
    @31
    @6
    @20
    cF
    wf
    @6
    cc
    @0
    wf
    @35
    wph
    @6
    @60
    @20
    cF
    wph
    cF
    wfun
    #
    @6
    @60
    cF
    wf
    wph
    @47
    @61
    @51
    @6
    cc
    cF
    ffun
    syl
    cF
    fdmrn
    sylib
    wph
    @60
    @20
    @21
    limccog.1
    difss2d
    fssd
    @6
    @20
    cc
    cG
    cF
    fco
    syl2anc
    @52
    @53
    @36
    ellimc2
    mpbir2and
end
