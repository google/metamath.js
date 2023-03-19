include "cv.mm"
include "cabs.mm"
include "ccom.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cicc.mm"
include "co.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "wcel.mm"
include "wa.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "cr.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "ccncf.mm"
include "wf.mm"
include "cncff.mm"
include "ffun.mm"
include "3syl.mm"
include "adantr.mm"
include "simpr.mm"
include "syl.mm"
include "fdm.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "fvco.mm"
include "syl2anc.mm"
include "ffvelrnda.mm"
include "eldifad.mm"
include "recnd.mm"
include "wne.mm"
include "eldifsni.mm"
include "absrpcld.mm"
include "eqeltrd.mm"
include "nfv.mm"
include "nfcv.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfco.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfral.mm"
include "nfan.mm"
include "fveq2.mm"
include "breq2d.mm"
include "rspccva.mm"
include "adantll.mm"
include "cc.mm"
include "absf.mm"
include "a1i.mm"
include "wss.mm"
include "difss.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "fssd.mm"
include "fcompt.mm"
include "fveq2d.mm"
include "cbvmpt.mm"
include "feq1dd.mm"
include "mptex2.mm"
include "fvmpt2d.mm"
include "mpteq2dva.mm"
include "3eqtrd.mm"
include "sseldi.mm"
include "abscld.mm"
include "ad4ant14.mm"
include "breqtrd.mm"
include "ex.mm"
include "ralrimi.mm"
include "nfeq2.mm"
include "breq1.mm"
include "ralbid.mm"
include "rspcev.mm"
include "ssid.mm"
include "cncfss.mm"
include "sseldd.mm"
include "abscncf.mm"
include "cncfco.mm"
include "evthicc.mm"
include "simprd.mm"
include "r19.29a.mm"

theorem cncficcgt0
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vz: setvar z
  let vk: setvar k
  assume cncficcgt0.f: |- F = ( x e. ( A [,] B ) |-> C )
  assume cncficcgt0.a: |- ( ph -> A e. RR )
  assume cncficcgt0.b: |- ( ph -> B e. RR )
  assume cncficcgt0.aleb: |- ( ph -> A <_ B )
  assume cncficcgt0.fcn: |- ( ph -> F e. ( ( A [,] B ) -cn-> ( RR \ { 0 } ) ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint F y
  disjoint ph x
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint A c
  disjoint A d
  disjoint c d
  disjoint c x
  disjoint d x
  disjoint c y
  disjoint A z
  disjoint x z
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B z
  disjoint C c
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F z
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint k x
  assert |- ( ph -> E. y e. RR+ A. x e. ( A [,] B ) y <_ ( abs ` C ) )

  proof
    wph
    vc
    cv
    #
    cabs
    cF
    ccom
    #
    cfv
    #
    vd
    cv
    #
    @1
    cfv
    #
    cle
    wbr
    #
    vd
    cA
    cB
    cicc
    co
    #
    wral
    #
    vy
    cv
    #
    cC
    cabs
    cfv
    #
    cle
    wbr
    #
    vx
    @6
    wral
    #
    vy
    crp
    wrex
    #
    vc
    @6
    wph
    @0
    @6
    wcel
    #
    wa
    #
    @7
    wa
    #
    @2
    crp
    wcel
    #
    @2
    @9
    cle
    wbr
    #
    vx
    @6
    wral
    #
    @12
    @14
    @16
    @7
    @14
    @2
    @0
    cF
    cfv
    #
    cabs
    cfv
    #
    crp
    @14
    cF
    wfun
    #
    @0
    cF
    cdm
    #
    wcel
    @2
    @20
    wceq
    wph
    @21
    @13
    wph
    cF
    @6
    cr
    cc0
    csn
    #
    cdif
    #
    ccncf
    co
    #
    wcel
    #
    @6
    @24
    cF
    wf
    #
    @21
    cncficcgt0.fcn
    @6
    @24
    cF
    cncff
    #
    @6
    @24
    cF
    ffun
    3syl
    adantr
    @14
    @0
    @6
    @22
    wph
    @13
    simpr
    wph
    @6
    @22
    wceq
    @13
    wph
    @22
    @6
    wph
    @27
    @22
    @6
    wceq
    wph
    @26
    @27
    cncficcgt0.fcn
    @28
    syl
    #
    @6
    @24
    cF
    fdm
    syl
    eqcomd
    adantr
    eleqtrd
    @0
    cabs
    cF
    fvco
    syl2anc
    @14
    @19
    @14
    @19
    @14
    @19
    cr
    @23
    wph
    @6
    @24
    @0
    cF
    @29
    ffvelrnda
    #
    eldifad
    recnd
    @14
    @19
    @24
    wcel
    @19
    cc0
    wne
    @30
    @19
    cr
    cc0
    eldifsni
    syl
    absrpcld
    eqeltrd
    adantr
    @15
    @17
    vx
    @6
    @14
    @7
    vx
    @14
    vx
    nfv
    @5
    vx
    vd
    @6
    vx
    @6
    nfcv
    vx
    @2
    @4
    cle
    vx
    @0
    @1
    vx
    cabs
    cF
    vx
    cabs
    nfcv
    #
    vx
    cF
    vx
    @6
    cC
    cmpt
    #
    cncficcgt0.f
    vx
    @6
    cC
    nfmpt1
    nfcxfr
    #
    nfco
    #
    vx
    @0
    nfcv
    nffv
    #
    vx
    cle
    nfcv
    vx
    @3
    @1
    @34
    vx
    @3
    nfcv
    nffv
    nfbr
    nfral
    nfan
    @15
    vx
    cv
    #
    @6
    wcel
    #
    @17
    @15
    @37
    wa
    @2
    @36
    @1
    cfv
    #
    @9
    cle
    @7
    @37
    @2
    @38
    cle
    wbr
    #
    @14
    @5
    @39
    vd
    @36
    @6
    @3
    @36
    wceq
    @4
    @38
    @2
    cle
    @3
    @36
    @1
    fveq2
    breq2d
    rspccva
    adantll
    wph
    @37
    @38
    @9
    wceq
    @13
    @7
    wph
    vx
    @6
    @9
    @1
    cr
    wph
    @1
    vz
    @6
    vz
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    cmpt
    #
    vx
    @6
    @36
    cF
    cfv
    #
    cabs
    cfv
    #
    cmpt
    #
    vx
    @6
    @9
    cmpt
    wph
    cc
    cr
    cabs
    wf
    #
    @6
    cc
    cF
    wf
    @1
    @43
    wceq
    @47
    wph
    absf
    a1i
    wph
    @6
    @24
    cc
    cF
    @29
    @24
    cc
    wss
    #
    wph
    @24
    cr
    cc
    cr
    @23
    difss
    ax-resscn
    sstri
    #
    a1i
    #
    fssd
    vz
    cabs
    cF
    @6
    cc
    cr
    fcompt
    syl2anc
    @43
    @46
    wceq
    wph
    vz
    vx
    @6
    @42
    @45
    vx
    @41
    cabs
    @31
    vx
    @40
    cF
    @33
    vx
    @40
    nfcv
    nffv
    nffv
    vz
    @45
    nfcv
    @40
    @36
    wceq
    @41
    @44
    cabs
    @40
    @36
    cF
    fveq2
    fveq2d
    cbvmpt
    a1i
    wph
    vx
    @6
    @45
    @9
    wph
    @37
    wa
    #
    @44
    cC
    cabs
    wph
    vx
    @6
    cC
    cF
    @24
    cF
    @32
    wceq
    wph
    cncficcgt0.f
    a1i
    #
    wph
    vx
    @6
    cC
    @24
    wph
    @6
    @24
    cF
    @32
    @52
    @29
    feq1dd
    mptex2
    #
    fvmpt2d
    fveq2d
    mpteq2dva
    3eqtrd
    @51
    cC
    @51
    @24
    cc
    cC
    @49
    @53
    sseldi
    abscld
    fvmpt2d
    ad4ant14
    breqtrd
    ex
    ralrimi
    @11
    @18
    vy
    @2
    crp
    @8
    @2
    wceq
    @10
    @17
    vx
    @6
    vx
    @8
    @2
    @35
    nfeq2
    @8
    @2
    @9
    cle
    breq1
    ralbid
    rspcev
    syl2anc
    wph
    vb
    cv
    @1
    cfv
    va
    cv
    @1
    cfv
    cle
    wbr
    vb
    @6
    wral
    va
    @6
    wrex
    @7
    vc
    @6
    wrex
    wph
    va
    vb
    vc
    vd
    cA
    cB
    @1
    cncficcgt0.a
    cncficcgt0.b
    cncficcgt0.aleb
    wph
    @6
    cc
    cr
    cF
    cabs
    wph
    @25
    @6
    cc
    ccncf
    co
    #
    cF
    wph
    @48
    cc
    cc
    wss
    #
    @25
    @54
    wss
    @50
    @55
    wph
    cc
    ssid
    a1i
    @6
    @24
    cc
    cncfss
    syl2anc
    cncficcgt0.fcn
    sseldd
    cabs
    cc
    cr
    ccncf
    co
    wcel
    wph
    abscncf
    a1i
    cncfco
    evthicc
    simprd
    r19.29a
end
