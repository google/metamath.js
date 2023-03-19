include "c1.mm"
include "cli.mm"
include "wbr.mm"
include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cle.mm"
include "corvc.mm"
include "co.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "cress.mm"
include "ctopn.mm"
include "clm.mm"
include "cdm.mm"
include "eqid.mm"
include "cprb.mm"
include "wcel.mm"
include "cmeas.mm"
include "domprobmeas.mm"
include "syl.mm"
include "wa.mm"
include "adantr.mm"
include "crrv.mm"
include "simpr.mm"
include "nnred.mm"
include "orvclteel.mm"
include "fmptd.mm"
include "caddc.mm"
include "peano2nnd.mm"
include "lep1d.mm"
include "orvclteinc.mm"
include "eqidd.mm"
include "wceq.mm"
include "oveq2d.mm"
include "fvmptd.mm"
include "3sstr4d.mm"
include "meascnbl.mm"
include "wf.mm"
include "wfn.mm"
include "measfn.mm"
include "dffn5.mm"
include "biimpi.mm"
include "3syl.mm"
include "prob01.mm"
include "sylan.mm"
include "fmpt3d.mm"
include "fco.mm"
include "syl2anc.mm"
include "dstfrvunirn.mm"
include "unveldomd.mm"
include "eqeltrd.mm"
include "cxr.mm"
include "clt.mm"
include "cico.mm"
include "wss.mm"
include "0xr.mm"
include "pnfxr.mm"
include "0le0.mm"
include "cr.mm"
include "1re.mm"
include "ltpnf.mm"
include "ax-mp.mm"
include "iccssico.mm"
include "mp4an.mm"
include "lmlimxrge0.mm"
include "mpbid.mm"
include "fveq2.mm"
include "fmptco.mm"
include "fveq2d.mm"
include "probvalrnd.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "probtot.mm"
include "eqtrd.mm"
include "3brtr3d.mm"
include "cz.mm"
include "cvv.mm"
include "wb.mm"
include "1z.mm"
include "reex.mm"
include "mptex.mm"
include "syl6eqel.mm"
include "nnuz.mm"
include "climmpt.mm"
include "sylancr.mm"
include "mpbird.mm"

theorem dstfrvclim1
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cF: class F
  let cX: class X
  let va: setvar a
  let vi: setvar i
  let vn: setvar n
  assume dstfrv.1: |- ( ph -> P e. Prob )
  assume dstfrv.2: |- ( ph -> X e. ( rRndVar ` P ) )
  assume dstfrv.3: |- ( ph -> F = ( x e. RR |-> ( P ` ( X oRVC <_ x ) ) ) )

  disjoint P x
  disjoint X x
  disjoint ph x
  disjoint a i
  disjoint a n
  disjoint a x
  disjoint P a
  disjoint i n
  disjoint i x
  disjoint P i
  disjoint n x
  disjoint P n
  disjoint X a
  disjoint X i
  disjoint X n
  disjoint F i
  disjoint a ph
  disjoint i ph
  disjoint n ph
  assert |- ( ph -> F ~~> 1 )

  proof
    wph
    cF
    c1
    cli
    wbr
    #
    vi
    cn
    vi
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    c1
    cli
    wbr
    #
    wph
    cP
    vi
    cn
    cX
    @1
    cle
    corvc
    #
    co
    #
    cmpt
    #
    ccom
    #
    @7
    crn
    cuni
    #
    cP
    cfv
    #
    @3
    c1
    cli
    wph
    @8
    @10
    cxrs
    cc0
    cpnf
    cicc
    co
    cress
    co
    ctopn
    cfv
    #
    clm
    cfv
    wbr
    @8
    @10
    cli
    wbr
    wph
    cP
    cdm
    #
    vn
    @7
    @11
    cP
    @11
    eqid
    #
    wph
    cP
    cprb
    wcel
    #
    cP
    @12
    cmeas
    cfv
    wcel
    #
    dstfrv.1
    cP
    domprobmeas
    syl
    #
    wph
    vi
    cn
    @6
    @12
    @7
    wph
    @1
    cn
    wcel
    #
    wa
    #
    @1
    cP
    cX
    wph
    @14
    @17
    dstfrv.1
    adantr
    #
    wph
    cX
    cP
    crrv
    cfv
    wcel
    #
    @17
    dstfrv.2
    adantr
    @18
    @1
    wph
    @17
    simpr
    nnred
    #
    orvclteel
    #
    @7
    eqid
    fmptd
    #
    wph
    vn
    cv
    #
    cn
    wcel
    #
    wa
    #
    cX
    @24
    @5
    co
    #
    cX
    @24
    c1
    caddc
    co
    #
    @5
    co
    #
    @24
    @7
    cfv
    @28
    @7
    cfv
    @26
    @24
    @28
    cP
    cX
    wph
    @14
    @25
    dstfrv.1
    adantr
    #
    wph
    @20
    @25
    dstfrv.2
    adantr
    #
    @26
    @24
    wph
    @25
    simpr
    #
    nnred
    #
    @26
    @28
    @26
    @24
    @32
    peano2nnd
    #
    nnred
    #
    @26
    @24
    @33
    lep1d
    orvclteinc
    @26
    vi
    @24
    @6
    @27
    cn
    @7
    @12
    @26
    @7
    eqidd
    #
    @26
    @1
    @24
    wceq
    #
    wa
    @1
    @24
    cX
    @5
    @26
    @37
    simpr
    oveq2d
    @32
    @26
    @24
    cP
    cX
    @30
    @31
    @33
    orvclteel
    fvmptd
    @26
    vi
    @28
    @6
    @29
    cn
    @7
    @12
    @36
    @26
    @1
    @28
    wceq
    #
    wa
    @1
    @28
    cX
    @5
    @26
    @38
    simpr
    oveq2d
    @34
    @26
    @28
    cP
    cX
    @30
    @31
    @35
    orvclteel
    fvmptd
    3sstr4d
    meascnbl
    wph
    @10
    @8
    @11
    cc0
    c1
    cicc
    co
    #
    @13
    wph
    @12
    @39
    cP
    wf
    cn
    @12
    @7
    wf
    cn
    @39
    @8
    wf
    wph
    va
    @12
    va
    cv
    #
    cP
    cfv
    #
    @39
    cP
    wph
    @15
    cP
    @12
    wfn
    #
    cP
    va
    @12
    @41
    cmpt
    wceq
    #
    @16
    @12
    cP
    measfn
    @42
    @43
    va
    @12
    cP
    dffn5
    biimpi
    3syl
    #
    wph
    @14
    @40
    @12
    wcel
    @41
    @39
    wcel
    dstfrv.1
    @40
    cP
    prob01
    sylan
    fmpt3d
    @23
    cn
    @12
    @39
    cP
    @7
    fco
    syl2anc
    wph
    @14
    @9
    @12
    wcel
    @10
    @39
    wcel
    dstfrv.1
    wph
    @9
    @12
    cuni
    #
    @12
    wph
    cP
    vi
    cX
    dstfrv.1
    dstfrv.2
    dstfrvunirn
    #
    wph
    cP
    dstfrv.1
    unveldomd
    eqeltrd
    @9
    cP
    prob01
    syl2anc
    cc0
    cxr
    wcel
    cpnf
    cxr
    wcel
    cc0
    cc0
    cle
    wbr
    c1
    cpnf
    clt
    wbr
    #
    @39
    cc0
    cpnf
    cico
    co
    wss
    0xr
    pnfxr
    0le0
    c1
    cr
    wcel
    @47
    1re
    c1
    ltpnf
    ax-mp
    cc0
    cpnf
    cc0
    c1
    iccssico
    mp4an
    lmlimxrge0
    mpbid
    wph
    @8
    vi
    cn
    @6
    cP
    cfv
    #
    cmpt
    @3
    wph
    vi
    va
    cn
    @12
    @6
    @41
    @48
    @7
    cP
    @22
    wph
    @7
    eqidd
    @44
    @40
    @6
    cP
    fveq2
    fmptco
    wph
    vi
    cn
    @2
    @48
    @18
    vx
    @1
    cX
    vx
    cv
    #
    @5
    co
    #
    cP
    cfv
    #
    @48
    cr
    cF
    cr
    wph
    cF
    vx
    cr
    @51
    cmpt
    #
    wceq
    @17
    dstfrv.3
    adantr
    @18
    @49
    @1
    wceq
    #
    wa
    #
    @50
    @6
    cP
    @54
    @49
    @1
    cX
    @5
    @18
    @53
    simpr
    oveq2d
    fveq2d
    @21
    @18
    @6
    cP
    @19
    @22
    probvalrnd
    fvmptd
    mpteq2dva
    eqtr4d
    wph
    @10
    @45
    cP
    cfv
    #
    c1
    wph
    @9
    @45
    cP
    @46
    fveq2d
    wph
    @14
    @55
    c1
    wceq
    dstfrv.1
    cP
    probtot
    syl
    eqtrd
    3brtr3d
    wph
    c1
    cz
    wcel
    cF
    cvv
    wcel
    @0
    @4
    wb
    1z
    wph
    cF
    @52
    cvv
    dstfrv.3
    vx
    cr
    @51
    reex
    mptex
    syl6eqel
    c1
    vi
    cF
    @3
    c1
    cvv
    cn
    nnuz
    @3
    eqid
    climmpt
    sylancr
    mpbird
end
