include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cfv.mm"
include "cfzo.mm"
include "ciun.mm"
include "cdif.mm"
include "cesum.mm"
include "cmpt.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "clm.mm"
include "wcel.mm"
include "wa.mm"
include "cmeas.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "adantr.mm"
include "csiga.mm"
include "measbase.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "wral.mm"
include "simpll.mm"
include "fzossnn.mm"
include "simpr.mm"
include "sseldi.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "sigaclfu2.mm"
include "difelsiga.mm"
include "syl3anc.mm"
include "measvxrge0.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2.mm"
include "iuneq1d.mm"
include "difeq12d.mm"
include "fveq2d.mm"
include "esumcvg2.mm"
include "wf.mm"
include "measfrge0.mm"
include "fcompt.mm"
include "caddc.mm"
include "nfcv.mm"
include "cz.mm"
include "nnzd.mm"
include "fzval3.mm"
include "olcd.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "measiuns.mm"
include "wfn.mm"
include "ffn.mm"
include "iuninc.mm"
include "eqtr3d.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "wrex.mm"
include "cab.mm"
include "dfiun2g.mm"
include "fnrnfv.mm"
include "unieqd.mm"
include "eqidd.mm"
include "orcd.mm"
include "3brtr4d.mm"

theorem meascnbl
  let wph: wff ph
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cM: class M
  let vi: setvar i
  let vk: setvar k
  let vo: setvar o
  let vp: setvar p
  let vx: setvar x
  assume meascnbl.0: |- J = ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) )
  assume meascnbl.1: |- ( ph -> M e. ( measures ` S ) )
  assume meascnbl.2: |- ( ph -> F : NN --> S )
  assume meascnbl.3: |- ( ( ph /\ n e. NN ) -> ( F ` n ) C_ ( F ` ( n + 1 ) ) )

  disjoint F n
  disjoint J n
  disjoint M n
  disjoint S n
  disjoint n ph
  disjoint i k
  disjoint i n
  disjoint i o
  disjoint i p
  disjoint i x
  disjoint F i
  disjoint k n
  disjoint k o
  disjoint k p
  disjoint k x
  disjoint F k
  disjoint n o
  disjoint n p
  disjoint n x
  disjoint o p
  disjoint o x
  disjoint F o
  disjoint p x
  disjoint F p
  disjoint F x
  disjoint J i
  disjoint M i
  disjoint M o
  disjoint M p
  disjoint S i
  disjoint S k
  disjoint i ph
  disjoint k ph
  disjoint o ph
  disjoint p ph
  assert |- ( ph -> ( M o. F ) ( ~~>t ` J ) ( M ` U. ran F ) )

  proof
    wph
    vi
    cn
    c1
    vi
    cv
    #
    cfz
    co
    #
    vn
    cv
    #
    cF
    cfv
    #
    vk
    c1
    @2
    cfzo
    co
    #
    vk
    cv
    #
    cF
    cfv
    #
    ciun
    #
    cdif
    #
    cM
    cfv
    #
    vn
    cesum
    #
    cmpt
    #
    cn
    @9
    vn
    cesum
    #
    cM
    cF
    ccom
    #
    cF
    crn
    #
    cuni
    #
    cM
    cfv
    #
    cJ
    clm
    cfv
    wph
    @9
    vo
    cv
    #
    cF
    cfv
    #
    vk
    c1
    @17
    cfzo
    co
    #
    @6
    ciun
    #
    cdif
    #
    cM
    cfv
    vp
    cv
    #
    cF
    cfv
    #
    vk
    c1
    @22
    cfzo
    co
    #
    @6
    ciun
    #
    cdif
    #
    cM
    cfv
    vn
    vp
    vi
    cJ
    vo
    meascnbl.0
    wph
    @2
    cn
    wcel
    #
    wa
    #
    cM
    cS
    cmeas
    cfv
    wcel
    #
    @8
    cS
    wcel
    #
    @9
    cc0
    cpnf
    cicc
    co
    #
    wcel
    wph
    @29
    @27
    meascnbl.1
    adantr
    @28
    cS
    csiga
    crn
    cuni
    wcel
    #
    @3
    cS
    wcel
    #
    @7
    cS
    wcel
    #
    @30
    wph
    @32
    @27
    wph
    @29
    @32
    meascnbl.1
    cS
    cM
    measbase
    syl
    adantr
    #
    wph
    cn
    cS
    @2
    cF
    meascnbl.2
    ffvelrnda
    #
    @28
    @32
    @6
    cS
    wcel
    #
    vk
    @4
    wral
    @34
    @35
    @28
    @37
    vk
    @4
    @28
    @5
    @4
    wcel
    #
    wa
    #
    wph
    @5
    cn
    wcel
    @37
    wph
    @27
    @38
    simpll
    @39
    @4
    cn
    @5
    @2
    fzossnn
    @28
    @38
    simpr
    sseldi
    wph
    cn
    cS
    @5
    cF
    meascnbl.2
    ffvelrnda
    syl2anc
    ralrimiva
    @6
    cS
    vk
    @2
    sigaclfu2
    syl2anc
    @3
    @7
    cS
    difelsiga
    syl3anc
    @8
    cS
    cM
    measvxrge0
    syl2anc
    @2
    @17
    wceq
    #
    @8
    @21
    cM
    @40
    @3
    @18
    @7
    @20
    @2
    @17
    cF
    fveq2
    @40
    vk
    @4
    @19
    @6
    @2
    @17
    c1
    cfzo
    oveq2
    iuneq1d
    difeq12d
    fveq2d
    @2
    @22
    wceq
    #
    @8
    @26
    cM
    @41
    @3
    @23
    @7
    @25
    @2
    @22
    cF
    fveq2
    @41
    vk
    @4
    @24
    @6
    @2
    @22
    c1
    cfzo
    oveq2
    iuneq1d
    difeq12d
    fveq2d
    esumcvg2
    wph
    @13
    vi
    cn
    @0
    cF
    cfv
    #
    cM
    cfv
    #
    cmpt
    #
    @11
    wph
    cS
    @31
    cM
    wf
    #
    cn
    cS
    cF
    wf
    #
    @13
    @44
    wceq
    wph
    @29
    @45
    meascnbl.1
    cS
    cM
    measfrge0
    syl
    meascnbl.2
    vi
    cM
    cF
    cn
    cS
    @31
    fcompt
    syl2anc
    wph
    vi
    cn
    @10
    @43
    wph
    @0
    cn
    wcel
    #
    wa
    #
    vn
    @1
    @3
    ciun
    #
    cM
    cfv
    @10
    @43
    @48
    @3
    @6
    cS
    vk
    vn
    @0
    c1
    caddc
    co
    #
    cM
    @1
    vn
    @6
    nfcv
    #
    @2
    @5
    cF
    fveq2
    #
    @48
    @1
    c1
    @50
    cfzo
    co
    #
    wceq
    #
    @1
    cn
    wceq
    @48
    @0
    cz
    wcel
    @54
    @48
    @0
    wph
    @47
    simpr
    nnzd
    c1
    @0
    fzval3
    syl
    #
    olcd
    wph
    @29
    @47
    meascnbl.1
    adantr
    @48
    @2
    @1
    wcel
    #
    wa
    #
    wph
    @27
    @33
    wph
    @47
    @56
    simpll
    @57
    @53
    cn
    @2
    @50
    fzossnn
    @48
    @56
    @2
    @53
    wcel
    @48
    @1
    @53
    @2
    @55
    eleq2d
    biimpa
    sseldi
    @36
    syl2anc
    measiuns
    @48
    @49
    @42
    cM
    wph
    vi
    vn
    cF
    wph
    @46
    cF
    cn
    wfn
    #
    meascnbl.2
    cn
    cS
    cF
    ffn
    syl
    #
    meascnbl.3
    iuninc
    fveq2d
    eqtr3d
    mpteq2dva
    eqtr4d
    wph
    vn
    cn
    @3
    ciun
    #
    cM
    cfv
    @16
    @12
    wph
    @60
    @15
    cM
    wph
    @60
    vx
    cv
    @3
    wceq
    vn
    cn
    wrex
    vx
    cab
    #
    cuni
    #
    @15
    wph
    @33
    vn
    cn
    wral
    @60
    @62
    wceq
    wph
    @33
    vn
    cn
    @36
    ralrimiva
    vn
    vx
    cn
    @3
    cS
    dfiun2g
    syl
    wph
    @14
    @61
    wph
    @58
    @14
    @61
    wceq
    @59
    vn
    vx
    cn
    cF
    fnrnfv
    syl
    unieqd
    eqtr4d
    fveq2d
    wph
    @3
    @6
    cS
    vk
    vn
    @50
    cM
    cn
    @51
    @52
    wph
    cn
    cn
    wceq
    cn
    @53
    wceq
    wph
    cn
    eqidd
    orcd
    meascnbl.1
    @36
    measiuns
    eqtr3d
    3brtr4d
end
