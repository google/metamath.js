include "ccfilu.mm"
include "cfv.mm"
include "wcel.mm"
include "cfbas.mm"
include "cv.mm"
include "cxp.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wf.mm"
include "cvv.mm"
include "cust.mm"
include "cfilufbas.mm"
include "syl2anc.mm"
include "cucn.mm"
include "co.mm"
include "wa.mm"
include "wbr.mm"
include "wi.mm"
include "isucn.mm"
include "simprbda.mm"
include "syl21anc.mm"
include "elfvexd.mm"
include "fbasrn.mm"
include "syl3anc.mm"
include "cop.mm"
include "cmpt2.mm"
include "ccnv.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "simplr.mm"
include "eqid.mm"
include "weq.mm"
include "imaeq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "wb.mm"
include "imaexg.mm"
include "elrnmpt.mm"
include "3syl.mm"
include "ad3antrrr.mm"
include "mpbird.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "eqtri.mm"
include "syl6eleqr.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "simplll.mm"
include "fbelss.mm"
include "sylan.mm"
include "fmucndlem.mm"
include "wfun.mm"
include "mpt2fun.mm"
include "funimass2.mm"
include "mpan.mm"
include "adantl.mm"
include "eqsstr3d.mm"
include "id.mm"
include "sqxpeqd.mm"
include "sseq1d.mm"
include "adantr.mm"
include "simpr.mm"
include "nfcv.mm"
include "simpl.mm"
include "fveq2d.mm"
include "opeq12d.mm"
include "cbvmpt2.mm"
include "ucnprima.mm"
include "cfiluexsm.mm"
include "r19.29a.mm"
include "ralrimiva.mm"
include "iscfilu.mm"
include "mpbir2and.mm"

theorem fmucnd
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cU: class U
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vc: setvar c
  let vb: setvar b
  let vv: setvar v
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  assume fmucnd.1: |- ( ph -> U e. ( UnifOn ` X ) )
  assume fmucnd.2: |- ( ph -> V e. ( UnifOn ` Y ) )
  assume fmucnd.3: |- ( ph -> F e. ( U uCn V ) )
  assume fmucnd.4: |- ( ph -> C e. ( CauFilU ` U ) )
  assume fmucnd.5: |- D = ran ( a e. C |-> ( F " a ) )

  disjoint C a
  disjoint D a
  disjoint F a
  disjoint V a
  disjoint X a
  disjoint Y a
  disjoint a ph
  disjoint a c
  disjoint C c
  disjoint a b
  disjoint a v
  disjoint b v
  disjoint D b
  disjoint D v
  disjoint a r
  disjoint a s
  disjoint a t
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b r
  disjoint b s
  disjoint b t
  disjoint b x
  disjoint b y
  disjoint F b
  disjoint c r
  disjoint c s
  disjoint c t
  disjoint c v
  disjoint c x
  disjoint c y
  disjoint F c
  disjoint r s
  disjoint r t
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint F r
  disjoint s t
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint F s
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint F t
  disjoint v x
  disjoint v y
  disjoint F v
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint U r
  disjoint U s
  disjoint U t
  disjoint U v
  disjoint U x
  disjoint U y
  disjoint V r
  disjoint V s
  disjoint V t
  disjoint V v
  disjoint V x
  disjoint V y
  disjoint X r
  disjoint X s
  disjoint X t
  disjoint X v
  disjoint X x
  disjoint X y
  disjoint Y r
  disjoint Y s
  disjoint Y v
  disjoint Y x
  disjoint ph s
  disjoint ph t
  disjoint ph v
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> D e. ( CauFilU ` V ) )

  proof
    wph
    cD
    cV
    ccfilu
    cfv
    wcel
    #
    cD
    cY
    cfbas
    cfv
    wcel
    #
    vb
    cv
    #
    @2
    cxp
    #
    vv
    cv
    #
    wss
    #
    vb
    cD
    wrex
    #
    vv
    cV
    wral
    #
    wph
    cC
    cX
    cfbas
    cfv
    wcel
    #
    cX
    cY
    cF
    wf
    #
    cY
    cvv
    wcel
    @1
    wph
    cU
    cX
    cust
    cfv
    wcel
    #
    cC
    cU
    ccfilu
    cfv
    wcel
    #
    @8
    fmucnd.1
    fmucnd.4
    cU
    cC
    cX
    cfilufbas
    syl2anc
    #
    wph
    @10
    cV
    cY
    cust
    cfv
    wcel
    #
    cF
    cU
    cV
    cucn
    co
    #
    wcel
    #
    @9
    fmucnd.1
    fmucnd.2
    fmucnd.3
    @10
    @13
    wa
    @15
    @9
    vx
    cv
    #
    vy
    cv
    #
    vr
    cv
    wbr
    @16
    cF
    cfv
    #
    @17
    cF
    cfv
    #
    @4
    wbr
    wi
    vy
    cX
    wral
    vx
    cX
    wral
    vr
    cU
    wrex
    vv
    cV
    wral
    vx
    vy
    cU
    cF
    cV
    cX
    cY
    vv
    vr
    isucn
    simprbda
    syl21anc
    #
    wph
    cV
    cust
    cY
    fmucnd.2
    elfvexd
    va
    cC
    cD
    cF
    cvv
    cX
    cY
    fmucnd.5
    fbasrn
    syl3anc
    wph
    @6
    vv
    cV
    wph
    @4
    cV
    wcel
    #
    wa
    #
    va
    cv
    #
    @23
    cxp
    #
    vx
    vy
    cX
    cX
    @18
    @19
    cop
    #
    cmpt2
    #
    ccnv
    @4
    cima
    #
    wss
    #
    @6
    va
    cC
    @22
    @23
    cC
    wcel
    #
    wa
    #
    @28
    wa
    #
    cF
    @23
    cima
    #
    cD
    wcel
    @32
    @32
    cxp
    #
    @4
    wss
    #
    @6
    @31
    @32
    vc
    cC
    cF
    vc
    cv
    #
    cima
    #
    cmpt
    #
    crn
    #
    cD
    @31
    @32
    @38
    wcel
    #
    @32
    @36
    wceq
    #
    vc
    cC
    wrex
    #
    @31
    @29
    @32
    @32
    wceq
    #
    @41
    @22
    @29
    @28
    simplr
    #
    @32
    eqid
    @40
    @42
    vc
    @23
    cC
    vc
    va
    weq
    @36
    @32
    @32
    @35
    @23
    cF
    imaeq2
    eqeq2d
    rspcev
    sylancl
    wph
    @39
    @41
    wb
    #
    @21
    @29
    @28
    wph
    @15
    @32
    cvv
    wcel
    @44
    fmucnd.3
    cF
    @23
    @14
    imaexg
    vc
    cC
    @36
    @32
    @37
    cvv
    @37
    eqid
    elrnmpt
    3syl
    ad3antrrr
    mpbird
    cD
    va
    cC
    @32
    cmpt
    #
    crn
    @38
    fmucnd.5
    @45
    @37
    va
    vc
    cC
    @32
    @36
    @23
    @35
    cF
    imaeq2
    cbvmptv
    rneqi
    eqtri
    syl6eleqr
    @31
    @33
    @26
    @24
    cima
    #
    @4
    @31
    cF
    cX
    wfn
    #
    @23
    cX
    wss
    #
    @46
    @33
    wceq
    wph
    @47
    @21
    @29
    @28
    wph
    @9
    @47
    @20
    cX
    cY
    cF
    ffn
    syl
    ad3antrrr
    @31
    wph
    @29
    @48
    wph
    @21
    @29
    @28
    simplll
    @43
    wph
    @8
    @29
    @48
    @12
    cX
    cC
    @23
    fbelss
    sylan
    syl2anc
    vx
    vy
    @23
    cF
    cX
    fmucndlem
    syl2anc
    @28
    @46
    @4
    wss
    #
    @30
    @26
    wfun
    @28
    @49
    vx
    vy
    cX
    cX
    @25
    @26
    @26
    eqid
    mpt2fun
    @24
    @4
    @26
    funimass2
    mpan
    adantl
    eqsstr3d
    @5
    @34
    vb
    @32
    cD
    @2
    @32
    wceq
    #
    @3
    @33
    @4
    @50
    @2
    @32
    @50
    id
    sqxpeqd
    sseq1d
    rspcev
    syl2anc
    @22
    @10
    @11
    @27
    cU
    wcel
    @28
    va
    cC
    wrex
    wph
    @10
    @21
    fmucnd.1
    adantr
    #
    wph
    @11
    @21
    fmucnd.4
    adantr
    @22
    vs
    vt
    cU
    cF
    @26
    cV
    @4
    cX
    cY
    @51
    wph
    @13
    @21
    fmucnd.2
    adantr
    wph
    @15
    @21
    fmucnd.3
    adantr
    wph
    @21
    simpr
    vx
    vy
    vs
    vt
    cX
    cX
    @25
    vs
    cv
    #
    cF
    cfv
    #
    vt
    cv
    #
    cF
    cfv
    #
    cop
    #
    vs
    @25
    nfcv
    vt
    @25
    nfcv
    vx
    @56
    nfcv
    vy
    @56
    nfcv
    vx
    vs
    weq
    #
    vy
    vt
    weq
    #
    wa
    #
    @18
    @53
    @19
    @55
    @59
    @16
    @52
    cF
    @57
    @58
    simpl
    fveq2d
    @59
    @17
    @54
    cF
    @57
    @58
    simpr
    fveq2d
    opeq12d
    cbvmpt2
    ucnprima
    cU
    cC
    @27
    cX
    va
    cfiluexsm
    syl3anc
    r19.29a
    ralrimiva
    wph
    @13
    @0
    @1
    @7
    wa
    wb
    fmucnd.2
    vv
    cV
    cD
    cY
    vb
    iscfilu
    syl
    mpbir2and
end
