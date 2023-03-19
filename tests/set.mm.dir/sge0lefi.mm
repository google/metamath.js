include "csumge0.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cres.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wral.mm"
include "wa.mm"
include "wcel.mm"
include "cxr.mm"
include "simpr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "adantr.mm"
include "wss.mm"
include "elpwinss.mm"
include "adantl.mm"
include "fssresd.mm"
include "sge0xrcl.mm"
include "adantlr.mm"
include "ad2antrr.mm"
include "sge0less.mm"
include "simplr.mm"
include "xrletrd.mm"
include "ralrimiva.mm"
include "ex.mm"
include "cmpt.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "sge0sup.mm"
include "wrex.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfel.mm"
include "wi.mm"
include "w3a.mm"
include "simp3.mm"
include "rspa.mm"
include "3adant3.mm"
include "eqbrtrd.mm"
include "3adant1l.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "rnmptss.mm"
include "syl.mm"
include "supxrleub.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "impbid.mm"

theorem sge0lefi
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cV: class V
  let cX: class X
  let vy: setvar y
  let vk: setvar k
  assume sge0lefi.1: |- ( ph -> X e. V )
  assume sge0lefi.2: |- ( ph -> F : X --> ( 0 [,] +oo ) )
  assume sge0lefi.3: |- ( ph -> A e. RR* )

  disjoint A x
  disjoint F x
  disjoint X x
  disjoint ph x
  disjoint A y
  disjoint x y
  disjoint F y
  disjoint X y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( ( sum^ ` F ) <_ A <-> A. x e. ( ~P X i^i Fin ) ( sum^ ` ( F |` x ) ) <_ A ) )

  proof
    wph
    cF
    csumge0
    cfv
    #
    cA
    cle
    wbr
    #
    cF
    vx
    cv
    #
    cres
    #
    csumge0
    cfv
    #
    cA
    cle
    wbr
    #
    vx
    cX
    cpw
    cfn
    cin
    #
    wral
    #
    wph
    @1
    @7
    wph
    @1
    wa
    #
    @5
    vx
    @6
    @8
    @2
    @6
    wcel
    #
    wa
    @4
    @0
    cA
    wph
    @9
    @4
    cxr
    wcel
    #
    @1
    wph
    @9
    wa
    #
    @3
    @6
    @2
    wph
    @9
    simpr
    @11
    cX
    cc0
    cpnf
    cicc
    co
    #
    @2
    cF
    wph
    cX
    @12
    cF
    wf
    @9
    sge0lefi.2
    adantr
    #
    @9
    @2
    cX
    wss
    wph
    @2
    cX
    cfn
    elpwinss
    adantl
    fssresd
    sge0xrcl
    #
    adantlr
    wph
    @0
    cxr
    wcel
    @1
    @9
    wph
    cF
    cV
    cX
    sge0lefi.1
    sge0lefi.2
    sge0xrcl
    ad2antrr
    wph
    cA
    cxr
    wcel
    #
    @1
    @9
    sge0lefi.3
    ad2antrr
    wph
    @9
    @4
    @0
    cle
    wbr
    @1
    @11
    cF
    cV
    cX
    @2
    wph
    cX
    cV
    wcel
    @9
    sge0lefi.1
    adantr
    @13
    sge0less
    adantlr
    wph
    @1
    @9
    simplr
    xrletrd
    ralrimiva
    ex
    wph
    @7
    @1
    wph
    @7
    wa
    #
    @0
    vx
    @6
    @4
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cA
    cle
    wph
    @0
    @19
    wceq
    @7
    wph
    vx
    cF
    cV
    cX
    sge0lefi.1
    sge0lefi.2
    sge0sup
    adantr
    @16
    @19
    cA
    cle
    wbr
    #
    vy
    cv
    #
    cA
    cle
    wbr
    #
    vy
    @18
    wral
    #
    @16
    @22
    vy
    @18
    @16
    @21
    @18
    wcel
    #
    wa
    #
    @21
    @4
    wceq
    #
    vx
    @6
    wrex
    #
    @22
    @24
    @27
    @16
    @24
    @27
    @21
    cvv
    wcel
    @24
    @27
    wb
    vy
    vex
    vx
    @6
    @4
    @21
    @17
    cvv
    @17
    eqid
    #
    elrnmpt
    ax-mp
    biimpi
    adantl
    @25
    @26
    @22
    vx
    @6
    @16
    @24
    vx
    wph
    @7
    vx
    wph
    vx
    nfv
    @5
    vx
    @6
    nfra1
    nfan
    vx
    @21
    @18
    vx
    @21
    nfcv
    vx
    @17
    vx
    @6
    @4
    nfmpt1
    nfrn
    nfel
    nfan
    @22
    vx
    nfv
    @16
    @9
    @26
    @22
    wi
    wi
    @24
    @16
    @9
    @26
    @22
    @7
    @9
    @26
    @22
    wph
    @7
    @9
    @26
    w3a
    @21
    @4
    cA
    cle
    @7
    @9
    @26
    simp3
    @7
    @9
    @5
    @26
    @5
    vx
    @6
    rspa
    3adant3
    eqbrtrd
    3adant1l
    3exp
    adantr
    rexlimd
    mpd
    ralrimiva
    @16
    @18
    cxr
    wss
    #
    @15
    @20
    @23
    wb
    wph
    @29
    @7
    wph
    @10
    vx
    @6
    wral
    @29
    wph
    @10
    vx
    @6
    @14
    ralrimiva
    vx
    @6
    @4
    cxr
    @17
    @28
    rnmptss
    syl
    adantr
    wph
    @15
    @7
    sge0lefi.3
    adantr
    vy
    @18
    cA
    supxrleub
    syl2anc
    mpbird
    eqbrtrd
    ex
    impbid
end
