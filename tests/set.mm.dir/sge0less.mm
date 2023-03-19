include "csumge0.mm"
include "cfv.mm"
include "cpnf.mm"
include "wceq.mm"
include "cres.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cxr.mm"
include "wcel.mm"
include "cvv.mm"
include "cin.mm"
include "inex1g.mm"
include "syl.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "fresin.mm"
include "sge0xrcl.mm"
include "pnfge.mm"
include "adantr.mm"
include "id.mm"
include "eqcomd.mm"
include "adantl.mm"
include "breqtrd.mm"
include "wn.mm"
include "cr.mm"
include "simpl.mm"
include "simpr.mm"
include "sge0repnf.mm"
include "mpbird.mm"
include "cpw.mm"
include "cfn.mm"
include "cv.mm"
include "csu.mm"
include "cmpt.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "wss.mm"
include "elinel1.mm"
include "elpwi.mm"
include "inss2.mm"
include "a1i.mm"
include "sstrd.mm"
include "sseldd.mm"
include "fvres.mm"
include "ralrimiva.mm"
include "sumeq2d.mm"
include "mpteq2ia.mm"
include "inss1.mm"
include "sspwb.mm"
include "biimpi.mm"
include "ax-mp.mm"
include "ssrin.mm"
include "mptss.mm"
include "eqsstri.mm"
include "rnss.mm"
include "sge0rern.mm"
include "fge0iccico.mm"
include "sge0rnre.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "supxrss.mm"
include "syl2anc.mm"
include "nelrnres.mm"
include "sge0reval.mm"
include "breq12d.mm"
include "pm2.61dan.mm"

theorem sge0less
  let wph: wff ph
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume sge0less.1: |- ( ph -> X e. V )
  assume sge0less.2: |- ( ph -> F : X --> ( 0 [,] +oo ) )


  assert |- ( ph -> ( sum^ ` ( F |` Y ) ) <_ ( sum^ ` F ) )

  proof
    wph
    cF
    csumge0
    cfv
    #
    cpnf
    wceq
    #
    cF
    cY
    cres
    #
    csumge0
    cfv
    #
    @0
    cle
    wbr
    #
    wph
    @1
    wa
    @3
    cpnf
    @0
    cle
    wph
    @3
    cpnf
    cle
    wbr
    #
    @1
    wph
    @3
    cxr
    wcel
    @5
    wph
    @2
    cvv
    cX
    cY
    cin
    #
    wph
    cX
    cV
    wcel
    #
    @6
    cvv
    wcel
    #
    sge0less.1
    cX
    cY
    cV
    inex1g
    #
    syl
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
    @6
    @10
    @2
    wf
    #
    sge0less.2
    cX
    @10
    cF
    cY
    fresin
    #
    syl
    sge0xrcl
    @3
    pnfge
    syl
    adantr
    @1
    cpnf
    @0
    wceq
    wph
    @1
    @0
    cpnf
    @1
    id
    eqcomd
    adantl
    breqtrd
    wph
    @1
    wn
    #
    wa
    #
    wph
    @0
    cr
    wcel
    #
    @4
    wph
    @14
    simpl
    #
    @15
    @16
    @14
    wph
    @14
    simpr
    @15
    cF
    cV
    cX
    @15
    wph
    @7
    @17
    sge0less.1
    syl
    @15
    wph
    @11
    @17
    sge0less.2
    syl
    sge0repnf
    mpbird
    wph
    @16
    wa
    #
    @4
    vx
    @6
    cpw
    #
    cfn
    cin
    #
    vx
    cv
    #
    vy
    cv
    #
    @2
    cfv
    #
    vy
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
    vx
    cX
    cpw
    #
    cfn
    cin
    #
    @21
    @22
    cF
    cfv
    #
    vy
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
    cle
    wbr
    #
    @18
    @26
    @33
    wss
    #
    @33
    cxr
    wss
    @35
    @36
    @18
    @25
    @32
    wss
    @36
    @25
    vx
    @20
    @31
    cmpt
    #
    @32
    vx
    @20
    @24
    @31
    @21
    @20
    wcel
    #
    @21
    @23
    @30
    vy
    @38
    @23
    @30
    wceq
    #
    vy
    @21
    @38
    @22
    @21
    wcel
    #
    wa
    #
    @22
    cY
    wcel
    @39
    @41
    @21
    cY
    @22
    @38
    @21
    cY
    wss
    @40
    @38
    @21
    @6
    cY
    @38
    @21
    @19
    wcel
    @21
    @6
    wss
    @21
    @19
    cfn
    elinel1
    @21
    @6
    elpwi
    syl
    @6
    cY
    wss
    @38
    cX
    cY
    inss2
    a1i
    sstrd
    adantr
    @38
    @40
    simpr
    sseldd
    @22
    cY
    cF
    fvres
    syl
    ralrimiva
    sumeq2d
    mpteq2ia
    @20
    @29
    wss
    #
    @37
    @32
    wss
    @19
    @28
    wss
    #
    @42
    @6
    cX
    wss
    #
    @43
    cX
    cY
    inss1
    @44
    @43
    @6
    cX
    sspwb
    biimpi
    ax-mp
    @19
    @28
    cfn
    ssrin
    ax-mp
    vx
    @20
    @29
    @31
    mptss
    ax-mp
    eqsstri
    @25
    @32
    rnss
    ax-mp
    a1i
    @18
    @33
    cr
    cxr
    @18
    vx
    vy
    cF
    cX
    @18
    cF
    cX
    wph
    @11
    @16
    sge0less.2
    adantr
    #
    @18
    cF
    cV
    cX
    wph
    @7
    @16
    sge0less.1
    adantr
    #
    @45
    wph
    @16
    simpr
    sge0rern
    #
    fge0iccico
    #
    sge0rnre
    ressxr
    syl6ss
    @26
    @33
    supxrss
    syl2anc
    @18
    @3
    @27
    @0
    @34
    cle
    @18
    vx
    vy
    @2
    cvv
    @6
    @18
    @7
    @8
    @46
    @9
    syl
    @18
    @2
    @6
    @18
    @11
    @12
    @45
    @13
    syl
    @18
    cpnf
    cF
    crn
    wcel
    wn
    cpnf
    @2
    crn
    wcel
    wn
    @47
    cpnf
    cF
    cY
    nelrnres
    syl
    fge0iccico
    sge0reval
    @18
    vx
    vy
    cF
    cV
    cX
    @46
    @48
    sge0reval
    breq12d
    mpbird
    syl2anc
    pm2.61dan
end
