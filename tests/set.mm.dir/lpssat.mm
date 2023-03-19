include "cv.mm"
include "wss.mm"
include "wn.mm"
include "wa.mm"
include "wral.mm"
include "wrex.mm"
include "wpss.mm"
include "dfpss3.mm"
include "simprbi.mm"
include "syl.mm"
include "wi.mm"
include "iman.mm"
include "ralbii.mm"
include "crab.mm"
include "ss2rab.mm"
include "cuni.mm"
include "clspn.mm"
include "cfv.mm"
include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "adantr.mm"
include "lsatlss.mm"
include "rabss2.mm"
include "uniss.mm"
include "4syl.mm"
include "wceq.mm"
include "unimax.mm"
include "eqid.mm"
include "lssss.mm"
include "eqsstrd.mm"
include "sstrd.mm"
include "adantl.mm"
include "lspss.mm"
include "syl3anc.mm"
include "lssats.mm"
include "syl2anc.mm"
include "3sstr4d.mm"
include "ex.mm"
include "syl5bir.mm"
include "mtod.mm"
include "dfrex2.mm"
include "sylibr.mm"

theorem lpssat
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cT: class T
  let cU: class U
  let cW: class W
  let vq: setvar q
  assume lpssat.s: |- S = ( LSubSp ` W )
  assume lpssat.a: |- A = ( LSAtoms ` W )
  assume lpssat.w: |- ( ph -> W e. LMod )
  assume lpssat.t: |- ( ph -> T e. S )
  assume lpssat.u: |- ( ph -> U e. S )
  assume lpssat.l: |- ( ph -> T C. U )

  disjoint A q
  disjoint S q
  disjoint T q
  disjoint U q
  disjoint W q
  assert |- ( ph -> E. q e. A ( q C_ U /\ -. q C_ T ) )

  proof
    wph
    vq
    cv
    #
    cU
    wss
    #
    @0
    cT
    wss
    #
    wn
    wa
    #
    wn
    #
    vq
    cA
    wral
    #
    wn
    @3
    vq
    cA
    wrex
    wph
    @5
    cU
    cT
    wss
    #
    wph
    cT
    cU
    wpss
    #
    @6
    wn
    #
    lpssat.l
    @7
    cT
    cU
    wss
    @8
    cT
    cU
    dfpss3
    simprbi
    syl
    @5
    @1
    @2
    wi
    #
    vq
    cA
    wral
    #
    wph
    @6
    @9
    @4
    vq
    cA
    @1
    @2
    iman
    ralbii
    @10
    @1
    vq
    cA
    crab
    #
    @2
    vq
    cA
    crab
    #
    wss
    #
    wph
    @6
    @1
    @2
    vq
    cA
    ss2rab
    wph
    @13
    @6
    wph
    @13
    wa
    #
    @11
    cuni
    #
    cW
    clspn
    cfv
    #
    cfv
    #
    @12
    cuni
    #
    @16
    cfv
    #
    cU
    cT
    @14
    cW
    clmod
    wcel
    #
    @18
    cW
    cbs
    cfv
    #
    wss
    #
    @15
    @18
    wss
    #
    @17
    @19
    wss
    wph
    @20
    @13
    lpssat.w
    adantr
    wph
    @22
    @13
    wph
    @18
    @2
    vq
    cS
    crab
    #
    cuni
    #
    @21
    wph
    @20
    cA
    cS
    wss
    @12
    @24
    wss
    @18
    @25
    wss
    lpssat.w
    cA
    cS
    cW
    lpssat.s
    lpssat.a
    lsatlss
    @2
    vq
    cA
    cS
    rabss2
    @12
    @24
    uniss
    4syl
    wph
    @25
    cT
    @21
    wph
    cT
    cS
    wcel
    #
    @25
    cT
    wceq
    lpssat.t
    vq
    cT
    cS
    unimax
    syl
    wph
    @26
    cT
    @21
    wss
    lpssat.t
    cS
    cT
    @21
    cW
    @21
    eqid
    #
    lpssat.s
    lssss
    syl
    eqsstrd
    sstrd
    adantr
    @13
    @23
    wph
    @11
    @12
    uniss
    adantl
    @15
    @18
    @16
    @21
    cW
    @27
    @16
    eqid
    #
    lspss
    syl3anc
    wph
    cU
    @17
    wceq
    #
    @13
    wph
    @20
    cU
    cS
    wcel
    @29
    lpssat.w
    lpssat.u
    vq
    cA
    cS
    cU
    @16
    cW
    lpssat.s
    @28
    lpssat.a
    lssats
    syl2anc
    adantr
    wph
    cT
    @19
    wceq
    #
    @13
    wph
    @20
    @26
    @30
    lpssat.w
    lpssat.t
    vq
    cA
    cS
    cT
    @16
    cW
    lpssat.s
    @28
    lpssat.a
    lssats
    syl2anc
    adantr
    3sstr4d
    ex
    syl5bir
    syl5bir
    mtod
    @3
    vq
    cA
    dfrex2
    sylibr
end
