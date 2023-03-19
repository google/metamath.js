include "wpss.mm"
include "clmod.mm"
include "wcel.mm"
include "w3a.mm"
include "wss.mm"
include "wn.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "dfpss3.mm"
include "simprbi.mm"
include "wral.mm"
include "crab.mm"
include "wi.mm"
include "ss2rab.mm"
include "iman.mm"
include "ralbii.mm"
include "bitr2i.mm"
include "cuni.mm"
include "clspn.mm"
include "cfv.mm"
include "cbs.mm"
include "simpl1.mm"
include "lsatlss.mm"
include "rabss2.mm"
include "uniss.mm"
include "4syl.mm"
include "wceq.mm"
include "simpl2.mm"
include "unimax.mm"
include "syl.mm"
include "eqid.mm"
include "lssss.mm"
include "eqsstrd.mm"
include "sstrd.mm"
include "adantl.mm"
include "lspss.mm"
include "syl3anc.mm"
include "simpl3.mm"
include "lssats.mm"
include "syl2anc.mm"
include "3sstr4d.mm"
include "ex.mm"
include "syl5bi.mm"
include "con3dimp.mm"
include "dfrex2.mm"
include "sylibr.mm"
include "sylan2.mm"

theorem lssat
  let cA: class A
  let cS: class S
  let cU: class U
  let cV: class V
  let cW: class W
  let vp: setvar p
  assume lssat.s: |- S = ( LSubSp ` W )
  assume lssat.a: |- A = ( LSAtoms ` W )

  disjoint A p
  disjoint S p
  disjoint U p
  disjoint V p
  disjoint W p
  assert |- ( ( ( W e. LMod /\ U e. S /\ V e. S ) /\ U C. V ) -> E. p e. A ( p C_ V /\ -. p C_ U ) )

  proof
    cU
    cV
    wpss
    #
    cW
    clmod
    wcel
    #
    cU
    cS
    wcel
    #
    cV
    cS
    wcel
    #
    w3a
    #
    cV
    cU
    wss
    #
    wn
    #
    vp
    cv
    #
    cV
    wss
    #
    @7
    cU
    wss
    #
    wn
    wa
    #
    vp
    cA
    wrex
    #
    @0
    cU
    cV
    wss
    @6
    cU
    cV
    dfpss3
    simprbi
    @4
    @6
    wa
    @10
    wn
    #
    vp
    cA
    wral
    #
    wn
    @11
    @4
    @13
    @5
    @13
    @8
    vp
    cA
    crab
    #
    @9
    vp
    cA
    crab
    #
    wss
    #
    @4
    @5
    @16
    @8
    @9
    wi
    #
    vp
    cA
    wral
    @13
    @8
    @9
    vp
    cA
    ss2rab
    @17
    @12
    vp
    cA
    @8
    @9
    iman
    ralbii
    bitr2i
    @4
    @16
    @5
    @4
    @16
    wa
    #
    @14
    cuni
    #
    cW
    clspn
    cfv
    #
    cfv
    #
    @15
    cuni
    #
    @20
    cfv
    #
    cV
    cU
    @18
    @1
    @22
    cW
    cbs
    cfv
    #
    wss
    @19
    @22
    wss
    #
    @21
    @23
    wss
    @1
    @2
    @3
    @16
    simpl1
    #
    @18
    @22
    @9
    vp
    cS
    crab
    #
    cuni
    #
    @24
    @18
    @1
    cA
    cS
    wss
    @15
    @27
    wss
    @22
    @28
    wss
    @26
    cA
    cS
    cW
    lssat.s
    lssat.a
    lsatlss
    @9
    vp
    cA
    cS
    rabss2
    @15
    @27
    uniss
    4syl
    @18
    @28
    cU
    @24
    @18
    @2
    @28
    cU
    wceq
    @1
    @2
    @3
    @16
    simpl2
    #
    vp
    cU
    cS
    unimax
    syl
    @18
    @2
    cU
    @24
    wss
    @29
    cS
    cU
    @24
    cW
    @24
    eqid
    #
    lssat.s
    lssss
    syl
    eqsstrd
    sstrd
    @16
    @25
    @4
    @14
    @15
    uniss
    adantl
    @19
    @22
    @20
    @24
    cW
    @30
    @20
    eqid
    #
    lspss
    syl3anc
    @18
    @1
    @3
    cV
    @21
    wceq
    @26
    @1
    @2
    @3
    @16
    simpl3
    vp
    cA
    cS
    cV
    @20
    cW
    lssat.s
    @31
    lssat.a
    lssats
    syl2anc
    @18
    @1
    @2
    cU
    @23
    wceq
    @26
    @29
    vp
    cA
    cS
    cU
    @20
    cW
    lssat.s
    @31
    lssat.a
    lssats
    syl2anc
    3sstr4d
    ex
    syl5bi
    con3dimp
    @10
    vp
    cA
    dfrex2
    sylibr
    sylan2
end
