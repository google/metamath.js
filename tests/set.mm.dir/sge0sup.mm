include "cpnf.mm"
include "crn.mm"
include "wcel.mm"
include "csumge0.mm"
include "cfv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "cres.mm"
include "cmpt.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "wa.mm"
include "eqidd.mm"
include "adantr.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "simpr.mm"
include "sge0pnfval.mm"
include "wss.mm"
include "wral.mm"
include "cvv.mm"
include "vex.mm"
include "a1i.mm"
include "elinel1.mm"
include "elpwi.mm"
include "syl.mm"
include "adantl.mm"
include "fssresd.mm"
include "sge0xrcl.mm"
include "adantlr.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "rnmptss.mm"
include "wrex.mm"
include "wb.mm"
include "wfn.mm"
include "ffn.mm"
include "fvelrnb.mm"
include "mpbid.mm"
include "wi.mm"
include "w3a.mm"
include "csn.mm"
include "snelpwi.mm"
include "snfi.mm"
include "elind.mm"
include "3ad2ant2.mm"
include "simp2.mm"
include "3ad2ant1.mm"
include "snssd.mm"
include "sge0sn.mm"
include "vsnid.mm"
include "fvres.mm"
include "ax-mp.mm"
include "simp3.mm"
include "3eqtrrd.mm"
include "reseq2.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "pnfex.mm"
include "elrnmptd.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "supxrpnf.mm"
include "3eqtr4d.mm"
include "wn.mm"
include "csu.mm"
include "fge0iccico.mm"
include "sge0reval.mm"
include "elinel2.mm"
include "nelrnres.mm"
include "ad2antlr.mm"
include "sge0fsum.mm"
include "sumeq2dv.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "eqtr4d.mm"
include "pm2.61dan.mm"

theorem sge0sup
  let wph: wff ph
  let vx: setvar x
  let cF: class F
  let cV: class V
  let cX: class X
  let vy: setvar y
  let vk: setvar k
  assume sge0sup.x: |- ( ph -> X e. V )
  assume sge0sup.f: |- ( ph -> F : X --> ( 0 [,] +oo ) )

  disjoint F x
  disjoint X x
  disjoint ph x
  disjoint F y
  disjoint x y
  disjoint X y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( sum^ ` F ) = sup ( ran ( x e. ( ~P X i^i Fin ) |-> ( sum^ ` ( F |` x ) ) ) , RR* , < ) )

  proof
    wph
    cpnf
    cF
    crn
    wcel
    #
    cF
    csumge0
    cfv
    #
    vx
    cX
    cpw
    #
    cfn
    cin
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
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    wceq
    wph
    @0
    wa
    #
    cpnf
    cpnf
    @1
    @9
    @10
    cpnf
    eqidd
    @10
    cF
    cV
    cX
    wph
    cX
    cV
    wcel
    #
    @0
    sge0sup.x
    adantr
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
    sge0sup.f
    adantr
    wph
    @0
    simpr
    #
    sge0pnfval
    @10
    @8
    cxr
    wss
    #
    cpnf
    @8
    wcel
    #
    @9
    cpnf
    wceq
    @10
    @6
    cxr
    wcel
    #
    vx
    @3
    wral
    @15
    @10
    @17
    vx
    @3
    wph
    @4
    @3
    wcel
    #
    @17
    @0
    wph
    @18
    wa
    #
    @5
    cvv
    @4
    @4
    cvv
    wcel
    @19
    vx
    vex
    a1i
    @19
    cX
    @12
    @4
    cF
    wph
    @13
    @18
    sge0sup.f
    adantr
    @18
    @4
    cX
    wss
    #
    wph
    @18
    @4
    @2
    wcel
    @20
    @4
    @2
    cfn
    elinel1
    @4
    cX
    elpwi
    syl
    adantl
    fssresd
    #
    sge0xrcl
    adantlr
    ralrimiva
    vx
    @3
    @6
    cxr
    @7
    @7
    eqid
    #
    rnmptss
    syl
    @10
    vy
    cv
    #
    cF
    cfv
    #
    cpnf
    wceq
    #
    vy
    cX
    wrex
    #
    @16
    @10
    @0
    @26
    @14
    wph
    @0
    @26
    wb
    #
    @0
    wph
    cF
    cX
    wfn
    #
    @27
    wph
    @13
    @28
    sge0sup.f
    cX
    @12
    cF
    ffn
    syl
    vy
    cX
    cpnf
    cF
    fvelrnb
    syl
    adantr
    mpbid
    wph
    @26
    @16
    wi
    @0
    wph
    @25
    @16
    vy
    cX
    wph
    @23
    cX
    wcel
    #
    @25
    @16
    wph
    @29
    @25
    w3a
    #
    vx
    @3
    @6
    cpnf
    @7
    cvv
    @22
    @30
    @23
    csn
    #
    @3
    wcel
    #
    cpnf
    cF
    @31
    cres
    #
    csumge0
    cfv
    #
    wceq
    #
    cpnf
    @6
    wceq
    #
    vx
    @3
    wrex
    @29
    wph
    @32
    @25
    @29
    @2
    cfn
    @31
    @23
    cX
    snelpwi
    @31
    cfn
    wcel
    @29
    @23
    snfi
    a1i
    elind
    3ad2ant2
    @30
    @34
    @23
    @33
    cfv
    #
    @24
    cpnf
    @30
    @23
    @33
    cX
    wph
    @29
    @25
    simp2
    #
    @30
    cX
    @12
    @31
    cF
    wph
    @29
    @13
    @25
    sge0sup.f
    3ad2ant1
    @30
    @23
    cX
    @38
    snssd
    fssresd
    sge0sn
    @37
    @24
    wceq
    #
    @30
    @23
    @31
    wcel
    @39
    vy
    vsnid
    @23
    @31
    cF
    fvres
    ax-mp
    a1i
    wph
    @29
    @25
    simp3
    3eqtrrd
    @36
    @35
    vx
    @31
    @3
    @4
    @31
    wceq
    #
    @6
    @34
    cpnf
    @40
    @5
    @33
    csumge0
    @4
    @31
    cF
    reseq2
    fveq2d
    eqeq2d
    rspcev
    syl2anc
    cpnf
    cvv
    wcel
    @30
    pnfex
    a1i
    elrnmptd
    3exp
    rexlimdv
    adantr
    mpd
    @8
    supxrpnf
    syl2anc
    3eqtr4d
    wph
    @0
    wn
    #
    wa
    #
    @1
    vx
    @3
    @4
    @24
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
    @9
    @42
    vx
    vy
    cF
    cV
    cX
    wph
    @11
    @41
    sge0sup.x
    adantr
    @42
    cF
    cX
    wph
    @13
    @41
    sge0sup.f
    adantr
    wph
    @41
    simpr
    fge0iccico
    sge0reval
    @42
    cxr
    @8
    @45
    clt
    @42
    @7
    @44
    @42
    vx
    @3
    @6
    @43
    @42
    @18
    wa
    #
    @6
    @4
    @23
    @5
    cfv
    #
    vy
    csu
    #
    @43
    @46
    vy
    @5
    @4
    @18
    @4
    cfn
    wcel
    @42
    @4
    @2
    cfn
    elinel2
    adantl
    @46
    @5
    @4
    wph
    @18
    @4
    @12
    @5
    wf
    @41
    @21
    adantlr
    @41
    cpnf
    @5
    crn
    wcel
    wn
    wph
    @18
    cpnf
    cF
    @4
    nelrnres
    ad2antlr
    fge0iccico
    sge0fsum
    @18
    @48
    @43
    wceq
    @42
    @18
    @4
    @47
    @24
    vy
    @18
    @23
    @4
    wcel
    #
    wa
    @49
    @47
    @24
    wceq
    @18
    @49
    simpr
    @23
    @4
    cF
    fvres
    syl
    sumeq2dv
    adantl
    eqtrd
    mpteq2dva
    rneqd
    supeq1d
    eqtr4d
    pm2.61dan
end
