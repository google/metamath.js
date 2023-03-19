include "wss.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "sstr.mm"
include "expcom.mm"
include "ralrimivw.mm"
include "crab.mm"
include "ss2rab.mm"
include "cuni.mm"
include "clspn.mm"
include "cfv.mm"
include "wa.mm"
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
include "syl.mm"
include "eqid.mm"
include "lssss.mm"
include "eqsstrd.mm"
include "sstrd.mm"
include "adantl.mm"
include "lspss.mm"
include "syl3anc.mm"
include "ex.mm"
include "lssats.mm"
include "syl2anc.mm"
include "sseq12d.mm"
include "sylibrd.mm"
include "syl5bir.mm"
include "impbid2.mm"

theorem lssatle
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cT: class T
  let cU: class U
  let cW: class W
  let vp: setvar p
  assume lssatle.s: |- S = ( LSubSp ` W )
  assume lssatle.a: |- A = ( LSAtoms ` W )
  assume lssatle.w: |- ( ph -> W e. LMod )
  assume lssatle.t: |- ( ph -> T e. S )
  assume lssatle.u: |- ( ph -> U e. S )

  disjoint A p
  disjoint S p
  disjoint T p
  disjoint U p
  disjoint W p
  assert |- ( ph -> ( T C_ U <-> A. p e. A ( p C_ T -> p C_ U ) ) )

  proof
    wph
    cT
    cU
    wss
    #
    vp
    cv
    #
    cT
    wss
    #
    @1
    cU
    wss
    #
    wi
    #
    vp
    cA
    wral
    #
    @0
    @4
    vp
    cA
    @2
    @0
    @3
    @1
    cT
    cU
    sstr
    expcom
    ralrimivw
    @5
    @2
    vp
    cA
    crab
    #
    @3
    vp
    cA
    crab
    #
    wss
    #
    wph
    @0
    @2
    @3
    vp
    cA
    ss2rab
    wph
    @8
    @6
    cuni
    #
    cW
    clspn
    cfv
    #
    cfv
    #
    @7
    cuni
    #
    @10
    cfv
    #
    wss
    #
    @0
    wph
    @8
    @14
    wph
    @8
    wa
    cW
    clmod
    wcel
    #
    @12
    cW
    cbs
    cfv
    #
    wss
    #
    @9
    @12
    wss
    #
    @14
    wph
    @15
    @8
    lssatle.w
    adantr
    wph
    @17
    @8
    wph
    @12
    @3
    vp
    cS
    crab
    #
    cuni
    #
    @16
    wph
    @15
    cA
    cS
    wss
    @7
    @19
    wss
    @12
    @20
    wss
    lssatle.w
    cA
    cS
    cW
    lssatle.s
    lssatle.a
    lsatlss
    @3
    vp
    cA
    cS
    rabss2
    @7
    @19
    uniss
    4syl
    wph
    @20
    cU
    @16
    wph
    cU
    cS
    wcel
    #
    @20
    cU
    wceq
    lssatle.u
    vp
    cU
    cS
    unimax
    syl
    wph
    @21
    cU
    @16
    wss
    lssatle.u
    cS
    cU
    @16
    cW
    @16
    eqid
    #
    lssatle.s
    lssss
    syl
    eqsstrd
    sstrd
    adantr
    @8
    @18
    wph
    @6
    @7
    uniss
    adantl
    @9
    @12
    @10
    @16
    cW
    @22
    @10
    eqid
    #
    lspss
    syl3anc
    ex
    wph
    cT
    @11
    cU
    @13
    wph
    @15
    cT
    cS
    wcel
    cT
    @11
    wceq
    lssatle.w
    lssatle.t
    vp
    cA
    cS
    cT
    @10
    cW
    lssatle.s
    @23
    lssatle.a
    lssats
    syl2anc
    wph
    @15
    @21
    cU
    @13
    wceq
    lssatle.w
    lssatle.u
    vp
    cA
    cS
    cU
    @10
    cW
    lssatle.s
    @23
    lssatle.a
    lssats
    syl2anc
    sseq12d
    sylibrd
    syl5bir
    impbid2
end
