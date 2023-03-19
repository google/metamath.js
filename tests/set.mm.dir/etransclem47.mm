include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "cfz.mm"
include "co.mm"
include "cmul.mm"
include "cmin.mm"
include "caddc.mm"
include "cxp.mm"
include "c1st.mm"
include "c2nd.mm"
include "cr.mm"
include "cdvn.mm"
include "csu.mm"
include "cfa.mm"
include "cdiv.mm"
include "cneg.mm"
include "wceq.mm"
include "a1i.mm"
include "cmpt.mm"
include "cicc.mm"
include "ceu.mm"
include "ccxp.mm"
include "wss.mm"
include "ssid.mm"
include "cc.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "reopn.mm"
include "eqid.mm"
include "tgioo2.mm"
include "eleqtri.mm"
include "cprime.mm"
include "cn.mm"
include "prmnn.mm"
include "syl.mm"
include "weq.mm"
include "fveq2.mm"
include "sumeq2ad.mm"
include "cbvmptv.mm"
include "negeq.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "negeqd.mm"
include "etransclem46.mm"
include "cfn.mm"
include "fzfid.mm"
include "xpfi.mm"
include "syl2anc.mm"
include "cn0.mm"
include "wf.mm"
include "cply.mm"
include "c0p.mm"
include "csn.mm"
include "eldifad.mm"
include "0zd.mm"
include "coef2.mm"
include "adantr.mm"
include "xp1st.mm"
include "elfznn0.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "zcnd.mm"
include "cdgr.mm"
include "dgrcl.mm"
include "syl5eqel.mm"
include "xp2nd.mm"
include "etransclem33.mm"
include "nn0red.mm"
include "mulcld.mm"
include "fsumcl.mm"
include "nnm1nn0.mm"
include "faccld.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divnegd.mm"
include "eqcomd.mm"
include "3eqtrd.mm"
include "etransclem45.mm"
include "znegcld.mm"
include "eqeltrd.mm"
include "syl5eq.mm"
include "divcld.mm"
include "etransclem44.mm"
include "negne0d.mm"
include "eqnetrd.mm"
include "cdif.mm"
include "eldifsni.mm"
include "ere.mm"
include "recni.mm"
include "dgrnznn.mm"
include "syl22anc.mm"
include "etransclem23.mm"
include "neeq1.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"

theorem etransclem47
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cP: class P
  let cQ: class Q
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cK: class K
  let cL: class L
  let cM: class M
  let vi: setvar i
  let vy: setvar y
  let vz: setvar z
  assume etransclem47.q: |- ( ph -> Q e. ( ( Poly ` ZZ ) \ { 0p } ) )
  assume etransclem47.qe0: |- ( ph -> ( Q ` _e ) = 0 )
  assume etransclem47.a: |- A = ( coeff ` Q )
  assume etransclem47.a0: |- ( ph -> ( A ` 0 ) =/= 0 )
  assume etransclem47.m: |- M = ( deg ` Q )
  assume etransclem47.p: |- ( ph -> P e. Prime )
  assume etransclem47.ap: |- ( ph -> ( abs ` ( A ` 0 ) ) < P )
  assume etransclem47.mp: |- ( ph -> ( ! ` M ) < P )
  assume etransclem47.9: |- ( ph -> ( sum_ j e. ( 0 ... M ) ( ( abs ` ( ( A ` j ) x. ( _e ^c j ) ) ) x. ( M x. ( M ^ ( M + 1 ) ) ) ) x. ( ( ( M ^ ( M + 1 ) ) ^ ( P - 1 ) ) / ( ! ` ( P - 1 ) ) ) ) < 1 )
  assume etransclem47.f: |- F = ( x e. RR |-> ( ( x ^ ( P - 1 ) ) x. prod_ j e. ( 1 ... M ) ( ( x - j ) ^ P ) ) )
  assume etransclem47.l: |- L = sum_ j e. ( 0 ... M ) ( ( ( A ` j ) x. ( _e ^c j ) ) x. S. ( 0 (,) j ) ( ( _e ^c -u x ) x. ( F ` x ) ) _d x )
  assume etransclem47.k: |- K = ( L / ( ! ` ( P - 1 ) ) )

  disjoint A j
  disjoint A k
  disjoint j k
  disjoint F j
  disjoint F k
  disjoint F x
  disjoint j x
  disjoint k x
  disjoint K k
  disjoint M j
  disjoint M k
  disjoint M x
  disjoint P j
  disjoint P k
  disjoint P x
  disjoint Q j
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint k x
  disjoint A i
  disjoint i j
  disjoint i k
  disjoint F i
  disjoint i x
  disjoint F y
  disjoint F z
  disjoint i y
  disjoint i z
  disjoint j y
  disjoint j z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint M i
  disjoint M y
  disjoint M z
  disjoint P i
  disjoint P y
  disjoint P z
  disjoint i ph
  assert |- ( ph -> E. k e. ZZ ( k =/= 0 /\ ( abs ` k ) < 1 ) )

  proof
    wph
    cK
    cz
    wcel
    cK
    cc0
    wne
    #
    cK
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    vk
    cv
    #
    cc0
    wne
    #
    @3
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    wa
    #
    vk
    cz
    wrex
    wph
    cK
    cc0
    cM
    cfz
    co
    #
    cc0
    cM
    cP
    cmul
    co
    cP
    c1
    cmin
    co
    #
    caddc
    co
    #
    cfz
    co
    #
    cxp
    #
    @3
    c1st
    cfv
    #
    cA
    cfv
    #
    @13
    @3
    c2nd
    cfv
    #
    cr
    cF
    cdvn
    co
    #
    cfv
    #
    cfv
    #
    cmul
    co
    #
    vk
    csu
    #
    @9
    cfa
    cfv
    #
    cdiv
    co
    #
    cneg
    #
    cz
    wph
    cK
    cL
    @21
    cdiv
    co
    #
    @20
    cneg
    @21
    cdiv
    co
    #
    @23
    cK
    @24
    wceq
    wph
    etransclem47.k
    a1i
    wph
    vx
    cA
    cP
    cQ
    @10
    vi
    vj
    vk
    cF
    vy
    cr
    @11
    vy
    cv
    #
    vi
    cv
    @16
    cfv
    #
    cfv
    #
    vi
    csu
    #
    cmpt
    #
    cL
    cM
    vz
    cc0
    vj
    cv
    cicc
    co
    #
    ceu
    vz
    cv
    #
    cneg
    #
    ccxp
    co
    #
    @32
    @30
    cfv
    #
    cmul
    co
    #
    cneg
    #
    cmpt
    etransclem47.q
    etransclem47.qe0
    etransclem47.a
    etransclem47.m
    cr
    cr
    wss
    wph
    cr
    ssid
    a1i
    cr
    cr
    cc
    cpr
    wcel
    #
    wph
    reelprrecn
    a1i
    cr
    ccnfld
    ctopn
    cfv
    #
    cr
    crest
    co
    #
    wcel
    #
    wph
    cr
    cioo
    crn
    ctg
    cfv
    @40
    reopn
    @39
    @39
    eqid
    tgioo2
    eleqtri
    #
    a1i
    wph
    cP
    cprime
    wcel
    cP
    cn
    wcel
    #
    etransclem47.p
    cP
    prmnn
    syl
    #
    etransclem47.f
    etransclem47.l
    @10
    eqid
    vy
    vx
    cr
    @29
    @11
    vx
    cv
    #
    @27
    cfv
    #
    vi
    csu
    vy
    vx
    weq
    @11
    @28
    @46
    vi
    @26
    @45
    @27
    fveq2
    sumeq2ad
    cbvmptv
    vz
    vx
    @31
    @37
    ceu
    @45
    cneg
    #
    ccxp
    co
    #
    @45
    @30
    cfv
    #
    cmul
    co
    #
    cneg
    vz
    vx
    weq
    #
    @36
    @50
    @51
    @34
    @48
    @35
    @49
    cmul
    @51
    @33
    @47
    ceu
    ccxp
    @32
    @45
    negeq
    oveq2d
    @32
    @45
    @30
    fveq2
    oveq12d
    negeqd
    cbvmptv
    etransclem46
    #
    wph
    @23
    @25
    wph
    @20
    @21
    wph
    @12
    @19
    vk
    wph
    @8
    cfn
    wcel
    @11
    cfn
    wcel
    @12
    cfn
    wcel
    wph
    cc0
    cM
    fzfid
    wph
    cc0
    @10
    fzfid
    @8
    @11
    xpfi
    syl2anc
    wph
    @3
    @12
    wcel
    #
    wa
    #
    @14
    @18
    @54
    @14
    @54
    cn0
    cz
    @13
    cA
    wph
    cn0
    cz
    cA
    wf
    #
    @53
    wph
    cQ
    cz
    cply
    cfv
    #
    wcel
    #
    cc0
    cz
    wcel
    @55
    wph
    cQ
    @56
    c0p
    csn
    #
    etransclem47.q
    eldifad
    #
    wph
    0zd
    cA
    cz
    cQ
    etransclem47.a
    coef2
    syl2anc
    #
    adantr
    @53
    @13
    cn0
    wcel
    #
    wph
    @53
    @13
    @8
    wcel
    @61
    @3
    @8
    @11
    xp1st
    @13
    cM
    elfznn0
    syl
    adantl
    #
    ffvelrnd
    zcnd
    @54
    cr
    cc
    @13
    @17
    @54
    vx
    cP
    cr
    vj
    cF
    cM
    @15
    cr
    @38
    @54
    reelprrecn
    a1i
    @41
    @54
    @42
    a1i
    wph
    @43
    @53
    @44
    adantr
    wph
    cM
    cn0
    wcel
    @53
    wph
    cM
    cQ
    cdgr
    cfv
    #
    cn0
    etransclem47.m
    wph
    @57
    @63
    cn0
    wcel
    @59
    cz
    cQ
    dgrcl
    syl
    syl5eqel
    #
    adantr
    etransclem47.f
    @53
    @15
    cn0
    wcel
    #
    wph
    @53
    @15
    @11
    wcel
    @65
    @3
    @8
    @11
    xp2nd
    @15
    @10
    elfznn0
    syl
    adantl
    etransclem33
    @54
    @13
    @62
    nn0red
    ffvelrnd
    mulcld
    fsumcl
    #
    wph
    @21
    wph
    @9
    wph
    @43
    @9
    cn0
    wcel
    @44
    cP
    nnm1nn0
    syl
    faccld
    #
    nncnd
    #
    wph
    @21
    @67
    nnne0d
    #
    divnegd
    eqcomd
    #
    3eqtrd
    wph
    @22
    wph
    vx
    cA
    cP
    @10
    vj
    vk
    cF
    @22
    cM
    @44
    @64
    etransclem47.f
    @60
    @22
    eqid
    #
    etransclem45
    znegcld
    eqeltrd
    wph
    cK
    @25
    cc0
    wph
    cK
    @24
    @25
    etransclem47.k
    @52
    syl5eq
    wph
    @25
    @23
    cc0
    @70
    wph
    @22
    wph
    @20
    @21
    @66
    @68
    @69
    divcld
    wph
    vx
    cA
    cP
    vj
    vk
    cF
    @22
    cM
    @60
    etransclem47.a0
    @64
    etransclem47.p
    etransclem47.ap
    etransclem47.mp
    etransclem47.f
    @71
    etransclem44
    negne0d
    eqnetrd
    eqnetrd
    wph
    vx
    cA
    cP
    vj
    cF
    cK
    cL
    cM
    @60
    etransclem47.l
    etransclem47.k
    @44
    wph
    cM
    @63
    cn
    etransclem47.m
    wph
    @57
    cQ
    c0p
    wne
    #
    ceu
    cc
    wcel
    #
    ceu
    cQ
    cfv
    cc0
    wceq
    @63
    cn
    wcel
    @59
    wph
    cQ
    @56
    @58
    cdif
    wcel
    @72
    etransclem47.q
    cQ
    @56
    c0p
    eldifsni
    syl
    @73
    wph
    ceu
    ere
    recni
    a1i
    etransclem47.qe0
    ceu
    cQ
    cz
    dgrnznn
    syl22anc
    syl5eqel
    etransclem47.f
    etransclem47.9
    etransclem23
    @7
    @0
    @2
    wa
    vk
    cK
    cz
    @3
    cK
    wceq
    #
    @4
    @0
    @6
    @2
    @3
    cK
    cc0
    neeq1
    @74
    @5
    @1
    c1
    clt
    @3
    cK
    cabs
    fveq2
    breq1d
    anbi12d
    rspcev
    syl12anc
end
