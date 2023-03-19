include "cof.mm"
include "cmpt.mm"
include "cseq.mm"
include "cfv.mm"
include "cv.mm"
include "csb.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "nfv.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "nfmpt.mm"
include "nfeq.mm"
include "nfim.mm"
include "weq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "mpteq2dv.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "cvv.mm"
include "sselda.mm"
include "adantr.mm"
include "mptexg.mm"
include "syl.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "simpll.mm"
include "simpr.mm"
include "syl12anc.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "chvar.mm"
include "nfcsb1v.mm"
include "nffv.mm"
include "csbeq1a.mm"
include "fveq1d.mm"
include "cbvmpt.mm"
include "syl6eq.mm"
include "seqof.mm"
include "nfseq.mm"
include "seqeq3d.mm"
include "syl6eqr.mm"

theorem seqof2
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vn: setvar n
  let vy: setvar y
  assume seqof2.1: |- ( ph -> A e. V )
  assume seqof2.2: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume seqof2.3: |- ( ph -> ( M ... N ) C_ B )
  assume seqof2.4: |- ( ( ph /\ ( x e. B /\ z e. A ) ) -> X e. W )

  disjoint x z
  disjoint A x
  disjoint A z
  disjoint M x
  disjoint M z
  disjoint N x
  disjoint N z
  disjoint ph x
  disjoint ph z
  disjoint .+ z
  disjoint B x
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint x y
  disjoint y z
  disjoint A y
  disjoint M n
  disjoint M y
  disjoint N n
  disjoint N y
  disjoint n ph
  disjoint ph y
  disjoint .+ n
  disjoint .+ y
  disjoint B n
  disjoint B y
  disjoint X n
  disjoint X y
  assert |- ( ph -> ( seq M ( oF .+ , ( x e. B |-> ( z e. A |-> X ) ) ) ` N ) = ( z e. A |-> ( seq M ( .+ , ( x e. B |-> X ) ) ` N ) ) )

  proof
    wph
    cN
    c.pl
    cof
    vx
    cB
    vz
    cA
    cX
    cmpt
    #
    cmpt
    #
    cM
    cseq
    cfv
    vy
    cA
    cN
    c.pl
    vz
    vy
    cv
    #
    vx
    cB
    cX
    cmpt
    #
    csb
    #
    cM
    cseq
    #
    cfv
    #
    cmpt
    vz
    cA
    cN
    c.pl
    @3
    cM
    cseq
    #
    cfv
    #
    cmpt
    wph
    vn
    vy
    cA
    c.pl
    @1
    @4
    cM
    cN
    cV
    seqof2.1
    seqof2.2
    wph
    vn
    cv
    #
    cM
    cN
    cfz
    co
    #
    wcel
    #
    wa
    #
    @9
    @1
    cfv
    #
    vz
    cA
    @9
    @3
    cfv
    #
    cmpt
    #
    vy
    cA
    @9
    @4
    cfv
    #
    cmpt
    wph
    vx
    cv
    #
    @10
    wcel
    #
    wa
    #
    @17
    @1
    cfv
    #
    vz
    cA
    @17
    @3
    cfv
    #
    cmpt
    #
    wceq
    #
    wi
    @12
    @13
    @15
    wceq
    #
    wi
    vx
    vn
    @12
    @24
    vx
    @12
    vx
    nfv
    vx
    @13
    @15
    vx
    cB
    @0
    @9
    nffvmpt1
    vx
    vz
    cA
    @14
    vx
    cA
    nfcv
    vx
    cB
    cX
    @9
    nffvmpt1
    nfmpt
    nfeq
    nfim
    vx
    vn
    weq
    #
    @19
    @12
    @23
    @24
    @25
    @18
    @11
    wph
    @17
    @9
    @10
    eleq1
    anbi2d
    @25
    @20
    @13
    @22
    @15
    @17
    @9
    @1
    fveq2
    @25
    vz
    cA
    @21
    @14
    @17
    @9
    @3
    fveq2
    mpteq2dv
    eqeq12d
    imbi12d
    @19
    @20
    @0
    @22
    @19
    @17
    cB
    wcel
    #
    @0
    cvv
    wcel
    #
    @20
    @0
    wceq
    wph
    @10
    cB
    @17
    seqof2.3
    sselda
    #
    @19
    cA
    cV
    wcel
    #
    @27
    wph
    @29
    @18
    seqof2.1
    adantr
    vz
    cA
    cX
    cV
    mptexg
    syl
    vx
    cB
    @0
    cvv
    @1
    @1
    eqid
    fvmpt2
    syl2anc
    @19
    vz
    cA
    @21
    cX
    @19
    vz
    cv
    cA
    wcel
    #
    wa
    #
    @26
    cX
    cW
    wcel
    #
    @21
    cX
    wceq
    @19
    @26
    @30
    @28
    adantr
    #
    @31
    wph
    @26
    @30
    @32
    wph
    @18
    @30
    simpll
    @33
    @19
    @30
    simpr
    seqof2.4
    syl12anc
    vx
    cB
    cX
    cW
    @3
    @3
    eqid
    fvmpt2
    syl2anc
    mpteq2dva
    eqtr4d
    chvar
    vz
    vy
    cA
    @14
    @16
    vy
    @14
    nfcv
    vz
    @9
    @4
    vz
    @2
    @3
    nfcsb1v
    #
    vz
    @9
    nfcv
    nffv
    vz
    vy
    weq
    #
    @9
    @3
    @4
    vz
    @2
    @3
    csbeq1a
    #
    fveq1d
    cbvmpt
    syl6eq
    seqof
    vz
    vy
    cA
    @8
    @6
    vy
    @8
    nfcv
    vz
    cN
    @5
    vz
    c.pl
    @4
    cM
    vz
    cM
    nfcv
    vz
    c.pl
    nfcv
    @34
    nfseq
    vz
    cN
    nfcv
    nffv
    @35
    cN
    @7
    @5
    @35
    @3
    @4
    c.pl
    cM
    @36
    seqeq3d
    fveq1d
    cbvmpt
    syl6eqr
end
