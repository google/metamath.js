include "cof.mm"
include "co.mm"
include "ccnv.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "cmpt.mm"
include "c1st.mm"
include "csn.mm"
include "c2nd.mm"
include "cin.mm"
include "ciun.mm"
include "ccom.mm"
include "nfmpt1.mm"
include "eqidd.mm"
include "cxp.mm"
include "wfn.mm"
include "cmpt2.mm"
include "wceq.mm"
include "fnov.mm"
include "sylib.mm"
include "ofoprabco.mm"
include "cnveqd.mm"
include "cnvco.mm"
include "syl6eq.mm"
include "imaeq1d.mm"
include "imaco.mm"
include "wbr.mm"
include "wrex.mm"
include "cab.mm"
include "dfima2.mm"
include "wcel.mm"
include "wa.mm"
include "vex.mm"
include "brcnv.mm"
include "cdm.mm"
include "wfun.mm"
include "wb.mm"
include "funmpt.mm"
include "funbrfv2b.mm"
include "ax-mp.mm"
include "opex.mm"
include "eqid.mm"
include "dmmpti.mm"
include "eleq2i.mm"
include "anbi1i.mm"
include "bitri.mm"
include "fveq2.mm"
include "opeq12d.mm"
include "fvmpt.mm"
include "eqeq1d.mm"
include "pm5.32i.mm"
include "3bitri.mm"
include "rexbii.mm"
include "abbii.mm"
include "nfv.mm"
include "nfab1.mm"
include "nfcv.mm"
include "eliun.mm"
include "wf.mm"
include "ffn.mm"
include "fniniseg.mm"
include "3syl.mm"
include "anbi12d.mm"
include "elin.mm"
include "anandi.mm"
include "3bitr4g.mm"
include "adantr.mm"
include "cnvimass.mm"
include "fndm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "sselda.mm"
include "1st2nd2.mm"
include "eqeq2.mm"
include "fvex.mm"
include "opth.mm"
include "syl6bb.mm"
include "anbi2d.mm"
include "bitr4d.mm"
include "rexbidva.mm"
include "abid.mm"
include "syl6bbr.mm"
include "syl5rbb.mm"
include "eqrd.mm"
include "syl5eq.mm"
include "eqtrd.mm"

theorem ofpreima
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  let cG: class G
  let cV: class V
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  assume ofpreima.1: |- ( ph -> F : A --> B )
  assume ofpreima.2: |- ( ph -> G : A --> C )
  assume ofpreima.3: |- ( ph -> A e. V )
  assume ofpreima.4: |- ( ph -> R Fn ( B X. C ) )

  disjoint A p
  disjoint D p
  disjoint F p
  disjoint G p
  disjoint R p
  disjoint p ph
  disjoint p q
  disjoint p s
  disjoint p x
  disjoint p y
  disjoint q s
  disjoint q x
  disjoint q y
  disjoint A q
  disjoint s x
  disjoint s y
  disjoint A s
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B s
  disjoint B x
  disjoint B y
  disjoint C s
  disjoint C x
  disjoint C y
  disjoint D q
  disjoint F q
  disjoint F s
  disjoint F x
  disjoint F y
  disjoint G q
  disjoint G s
  disjoint G x
  disjoint G y
  disjoint R q
  disjoint R s
  disjoint R x
  disjoint R y
  disjoint ph q
  disjoint ph s
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( `' ( F oF R G ) " D ) = U_ p e. ( `' R " D ) ( ( `' F " { ( 1st ` p ) } ) i^i ( `' G " { ( 2nd ` p ) } ) ) )

  proof
    wph
    cF
    cG
    cR
    cof
    co
    #
    ccnv
    #
    cD
    cima
    #
    vs
    cA
    vs
    cv
    #
    cF
    cfv
    #
    @3
    cG
    cfv
    #
    cop
    #
    cmpt
    #
    ccnv
    #
    cR
    ccnv
    #
    cD
    cima
    #
    cima
    #
    vp
    @10
    cF
    ccnv
    vp
    cv
    #
    c1st
    cfv
    #
    csn
    cima
    #
    cG
    ccnv
    @12
    c2nd
    cfv
    #
    csn
    cima
    #
    cin
    #
    ciun
    #
    wph
    @2
    @8
    @9
    ccom
    #
    cD
    cima
    @11
    wph
    @1
    @19
    cD
    wph
    @1
    cR
    @7
    ccom
    #
    ccnv
    @19
    wph
    @0
    @20
    wph
    vx
    vy
    cA
    cB
    cC
    cR
    cF
    cG
    @7
    cR
    cV
    vs
    vs
    cA
    @6
    nfmpt1
    ofpreima.1
    ofpreima.2
    ofpreima.3
    wph
    @7
    eqidd
    wph
    cR
    cB
    cC
    cxp
    #
    wfn
    #
    cR
    vx
    vy
    cB
    cC
    vx
    cv
    vy
    cv
    cR
    co
    cmpt2
    wceq
    ofpreima.4
    vx
    vy
    cB
    cC
    cR
    fnov
    sylib
    ofoprabco
    cnveqd
    cR
    @7
    cnvco
    syl6eq
    imaeq1d
    @8
    @9
    cD
    imaco
    syl6eq
    wph
    @11
    @12
    vq
    cv
    #
    @8
    wbr
    #
    vp
    @10
    wrex
    #
    vq
    cab
    #
    @18
    vp
    vq
    @8
    @10
    dfima2
    wph
    @26
    @23
    cA
    wcel
    #
    @23
    cF
    cfv
    #
    @23
    cG
    cfv
    #
    cop
    #
    @12
    wceq
    #
    wa
    #
    vp
    @10
    wrex
    #
    vq
    cab
    #
    @18
    @25
    @33
    vq
    @24
    @32
    vp
    @10
    @24
    @23
    @12
    @7
    wbr
    #
    @27
    @23
    @7
    cfv
    #
    @12
    wceq
    #
    wa
    #
    @32
    @12
    @23
    @7
    vp
    vex
    vq
    vex
    brcnv
    @35
    @23
    @7
    cdm
    #
    wcel
    #
    @37
    wa
    #
    @38
    @7
    wfun
    @35
    @41
    wb
    vs
    cA
    @6
    funmpt
    @23
    @12
    @7
    funbrfv2b
    ax-mp
    @40
    @27
    @37
    @39
    cA
    @23
    vs
    cA
    @6
    @7
    @4
    @5
    opex
    @7
    eqid
    #
    dmmpti
    eleq2i
    anbi1i
    bitri
    @27
    @37
    @31
    @27
    @36
    @30
    @12
    vs
    @23
    @6
    @30
    cA
    @7
    @3
    @23
    wceq
    @4
    @28
    @5
    @29
    @3
    @23
    cF
    fveq2
    @3
    @23
    cG
    fveq2
    opeq12d
    @42
    @28
    @29
    opex
    fvmpt
    eqeq1d
    pm5.32i
    3bitri
    rexbii
    abbii
    wph
    vq
    @34
    @18
    wph
    vq
    nfv
    @33
    vq
    nfab1
    vq
    @18
    nfcv
    @23
    @18
    wcel
    @23
    @17
    wcel
    #
    vp
    @10
    wrex
    #
    wph
    @23
    @34
    wcel
    #
    vp
    @23
    @10
    @17
    eliun
    wph
    @44
    @33
    @45
    wph
    @43
    @32
    vp
    @10
    wph
    @12
    @10
    wcel
    #
    wa
    #
    @43
    @27
    @28
    @13
    wceq
    #
    @29
    @15
    wceq
    #
    wa
    #
    wa
    #
    @32
    wph
    @43
    @51
    wb
    @46
    wph
    @23
    @14
    wcel
    #
    @23
    @16
    wcel
    #
    wa
    @27
    @48
    wa
    #
    @27
    @49
    wa
    #
    wa
    @43
    @51
    wph
    @52
    @54
    @53
    @55
    wph
    cA
    cB
    cF
    wf
    cF
    cA
    wfn
    @52
    @54
    wb
    ofpreima.1
    cA
    cB
    cF
    ffn
    cA
    @13
    @23
    cF
    fniniseg
    3syl
    wph
    cA
    cC
    cG
    wf
    cG
    cA
    wfn
    @53
    @55
    wb
    ofpreima.2
    cA
    cC
    cG
    ffn
    cA
    @15
    @23
    cG
    fniniseg
    3syl
    anbi12d
    @23
    @14
    @16
    elin
    @27
    @48
    @49
    anandi
    3bitr4g
    adantr
    @47
    @31
    @50
    @27
    @47
    @31
    @30
    @13
    @15
    cop
    #
    wceq
    #
    @50
    @47
    @12
    @21
    wcel
    @12
    @56
    wceq
    @31
    @57
    wb
    wph
    @10
    @21
    @12
    wph
    cR
    cdm
    #
    @10
    @21
    cR
    cD
    cnvimass
    wph
    @22
    @58
    @21
    wceq
    ofpreima.4
    @21
    cR
    fndm
    syl
    syl5sseq
    sselda
    @12
    cB
    cC
    1st2nd2
    @12
    @56
    @30
    eqeq2
    3syl
    @28
    @29
    @13
    @15
    @23
    cF
    fvex
    @23
    cG
    fvex
    opth
    syl6bb
    anbi2d
    bitr4d
    rexbidva
    @33
    vq
    abid
    syl6bbr
    syl5rbb
    eqrd
    syl5eq
    syl5eq
    eqtrd
end
