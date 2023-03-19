include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "wf.mm"
include "cicc.mm"
include "ffn.mm"
include "syl.mm"
include "cxr.mm"
include "0xr.mm"
include "a1i.mm"
include "pnfxr.mm"
include "iccssxr.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "cle.mm"
include "wbr.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "clt.mm"
include "crn.mm"
include "wn.mm"
include "adantr.mm"
include "simpr.mm"
include "xrlenltd.mm"
include "mpbird.mm"
include "xrgepnfd.mm"
include "eqcomd.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "wceq.mm"
include "fdm.mm"
include "eleqtrd.mm"
include "fvelrn.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "ad2antrr.mm"
include "condan.mm"
include "elicod.mm"
include "ralrimiva.mm"
include "jca.mm"
include "ffnfv.mm"
include "sylibr.mm"

theorem fge0iccico
  let wph: wff ph
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vk: setvar k
  assume fge0iccico.f: |- ( ph -> F : X --> ( 0 [,] +oo ) )
  assume fge0iccico.re: |- ( ph -> -. +oo e. ran F )


  assert |- ( ph -> F : X --> ( 0 [,) +oo ) )

  proof
    wph
    cF
    cX
    wfn
    #
    vx
    cv
    #
    cF
    cfv
    #
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    vx
    cX
    wral
    #
    wa
    cX
    @3
    cF
    wf
    wph
    @0
    @5
    wph
    cX
    cc0
    cpnf
    cicc
    co
    #
    cF
    wf
    #
    @0
    fge0iccico.f
    cX
    @6
    cF
    ffn
    syl
    wph
    @4
    vx
    cX
    wph
    @1
    cX
    wcel
    #
    wa
    #
    cc0
    cpnf
    @2
    cc0
    cxr
    wcel
    #
    @9
    0xr
    a1i
    #
    cpnf
    cxr
    wcel
    #
    @9
    pnfxr
    a1i
    #
    @9
    @6
    cxr
    @2
    cc0
    cpnf
    iccssxr
    wph
    cX
    @6
    @1
    cF
    fge0iccico.f
    ffvelrnda
    #
    sseldi
    #
    @9
    @10
    @12
    @2
    @6
    wcel
    cc0
    @2
    cle
    wbr
    @11
    @13
    @14
    cc0
    cpnf
    @2
    iccgelb
    syl3anc
    @9
    @2
    cpnf
    clt
    wbr
    #
    cpnf
    cF
    crn
    #
    wcel
    #
    @9
    @16
    wn
    #
    wa
    #
    cpnf
    @2
    @17
    @20
    @2
    cpnf
    @20
    @2
    @9
    @2
    cxr
    wcel
    @19
    @15
    adantr
    #
    @20
    cpnf
    @2
    cle
    wbr
    @19
    @9
    @19
    simpr
    @20
    cpnf
    @2
    @12
    @20
    pnfxr
    a1i
    @21
    xrlenltd
    mpbird
    xrgepnfd
    eqcomd
    @9
    @2
    @17
    wcel
    #
    @19
    @9
    cF
    wfun
    #
    @1
    cF
    cdm
    #
    wcel
    @22
    wph
    @23
    @8
    wph
    @7
    @23
    fge0iccico.f
    cX
    @6
    cF
    ffun
    syl
    adantr
    @9
    @1
    cX
    @24
    wph
    @8
    simpr
    wph
    cX
    @24
    wceq
    #
    @8
    wph
    @7
    @25
    fge0iccico.f
    @7
    @24
    cX
    cX
    @6
    cF
    fdm
    eqcomd
    syl
    adantr
    eleqtrd
    @1
    cF
    fvelrn
    syl2anc
    adantr
    eqeltrd
    wph
    @18
    wn
    @8
    @19
    fge0iccico.re
    ad2antrr
    condan
    elicod
    ralrimiva
    jca
    vx
    cX
    @3
    cF
    ffnfv
    sylibr
end
