include "csumge0.mm"
include "cfv.mm"
include "cv.mm"
include "csu.mm"
include "cfn.mm"
include "fge0icoicc.mm"
include "sge0xrcl.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cr.mm"
include "rge0ssre.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "fsumrecl.mm"
include "rexrd.mm"
include "cpw.mm"
include "cin.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cle.mm"
include "sge0reval.mm"
include "wbr.mm"
include "wral.mm"
include "wceq.mm"
include "wrex.mm"
include "simpr.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "a1i.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "syl.mm"
include "mpbid.mm"
include "wi.mm"
include "w3a.mm"
include "simp3.mm"
include "adantr.mm"
include "wf.mm"
include "fge0npnf.mm"
include "fge0iccre.mm"
include "ffvelrnd.mm"
include "cicc.mm"
include "0xr.mm"
include "pnfxr.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "wss.mm"
include "elinel1.mm"
include "elpwi.mm"
include "adantl.mm"
include "fsumless.mm"
include "3adant3.mm"
include "eqbrtrd.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "elinel2.mm"
include "sselda.mm"
include "rnmptss.mm"
include "supxrleub.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ssid.mm"
include "fsumlesge0.mm"
include "xrletrid.mm"

theorem sge0fsum
  let wph: wff ph
  let vx: setvar x
  let cF: class F
  let cX: class X
  let vw: setvar w
  let vy: setvar y
  let vk: setvar k
  assume sge0fsum.x: |- ( ph -> X e. Fin )
  assume sge0fsum.f: |- ( ph -> F : X --> ( 0 [,) +oo ) )

  disjoint F x
  disjoint X x
  disjoint ph x
  disjoint F w
  disjoint F y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint X w
  disjoint X y
  disjoint ph w
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( sum^ ` F ) = sum_ x e. X ( F ` x ) )

  proof
    wph
    cF
    csumge0
    cfv
    #
    cX
    vx
    cv
    #
    cF
    cfv
    #
    vx
    csu
    #
    wph
    cF
    cfn
    cX
    sge0fsum.x
    wph
    cF
    cX
    sge0fsum.f
    fge0icoicc
    #
    sge0xrcl
    wph
    @3
    wph
    cX
    @2
    vx
    sge0fsum.x
    wph
    @1
    cX
    wcel
    #
    wa
    cc0
    cpnf
    cico
    co
    #
    cr
    @2
    rge0ssre
    wph
    cX
    @6
    @1
    cF
    sge0fsum.f
    ffvelrnda
    sseldi
    fsumrecl
    rexrd
    #
    wph
    @0
    vy
    cX
    cpw
    #
    cfn
    cin
    #
    vy
    cv
    #
    @2
    vx
    csu
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    @3
    cle
    wph
    vy
    vx
    cF
    cfn
    cX
    sge0fsum.x
    sge0fsum.f
    sge0reval
    wph
    @14
    @3
    cle
    wbr
    #
    vw
    cv
    #
    @3
    cle
    wbr
    #
    vw
    @13
    wral
    #
    wph
    @17
    vw
    @13
    wph
    @16
    @13
    wcel
    #
    wa
    #
    @16
    @11
    wceq
    #
    vy
    @9
    wrex
    #
    @17
    @20
    @19
    @22
    wph
    @19
    simpr
    @20
    @16
    cvv
    wcel
    #
    @19
    @22
    wb
    @23
    @20
    vw
    vex
    a1i
    vy
    @9
    @11
    @16
    @12
    cvv
    @12
    eqid
    #
    elrnmpt
    syl
    mpbid
    wph
    @22
    @17
    wi
    @19
    wph
    @21
    @17
    vy
    @9
    wph
    @10
    @9
    wcel
    #
    @21
    @17
    wph
    @25
    @21
    w3a
    @16
    @11
    @3
    cle
    wph
    @25
    @21
    simp3
    wph
    @25
    @11
    @3
    cle
    wbr
    @21
    wph
    @25
    wa
    #
    cX
    @2
    @10
    vx
    wph
    cX
    cfn
    wcel
    @25
    sge0fsum.x
    adantr
    @26
    @5
    wa
    #
    cX
    cr
    @1
    cF
    @26
    cX
    cr
    cF
    wf
    #
    @5
    wph
    @28
    @25
    wph
    cF
    cX
    @4
    wph
    cF
    cX
    sge0fsum.f
    fge0npnf
    fge0iccre
    adantr
    #
    adantr
    @26
    @5
    simpr
    ffvelrnd
    @27
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    @2
    cc0
    cpnf
    cicc
    co
    #
    wcel
    cc0
    @2
    cle
    wbr
    @30
    @27
    0xr
    a1i
    @31
    @27
    pnfxr
    a1i
    @26
    cX
    @32
    @1
    cF
    wph
    cX
    @32
    cF
    wf
    @25
    @4
    adantr
    ffvelrnda
    cc0
    cpnf
    @2
    iccgelb
    syl3anc
    @25
    @10
    cX
    wss
    #
    wph
    @25
    @10
    @8
    wcel
    @33
    @10
    @8
    cfn
    elinel1
    @10
    cX
    elpwi
    syl
    adantl
    #
    fsumless
    3adant3
    eqbrtrd
    3exp
    rexlimdv
    adantr
    mpd
    ralrimiva
    wph
    @13
    cxr
    wss
    #
    @3
    cxr
    wcel
    @15
    @18
    wb
    wph
    @11
    cxr
    wcel
    #
    vy
    @9
    wral
    @35
    wph
    @36
    vy
    @9
    @26
    @11
    @26
    @10
    @2
    vx
    @25
    @10
    cfn
    wcel
    wph
    @10
    @8
    cfn
    elinel2
    adantl
    @26
    @1
    @10
    wcel
    #
    wa
    cX
    cr
    @1
    cF
    @26
    @28
    @37
    @29
    adantr
    @26
    @10
    cX
    @1
    @34
    sselda
    ffvelrnd
    fsumrecl
    rexrd
    ralrimiva
    vy
    @9
    @11
    cxr
    @12
    @24
    rnmptss
    syl
    @7
    vw
    @13
    @3
    supxrleub
    syl2anc
    mpbird
    eqbrtrd
    wph
    vx
    cF
    cfn
    cX
    cX
    sge0fsum.x
    sge0fsum.f
    cX
    cX
    wss
    wph
    cX
    ssid
    a1i
    sge0fsum.x
    fsumlesge0
    xrletrid
end
