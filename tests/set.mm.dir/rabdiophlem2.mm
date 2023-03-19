include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "cmpt.mm"
include "cmzp.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "cres.mm"
include "csb.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmpt.mm"
include "fveq1i.mm"
include "wceq.mm"
include "mapfzcons1cl.mm"
include "adantl.mm"
include "wral.mm"
include "wf.mm"
include "mzpf.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "ad2antlr.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "rspc.mm"
include "sylc.mm"
include "csbeq1.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "syl5req.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "wss.mm"
include "ovexd.mm"
include "caddc.mm"
include "fzssp1.mm"
include "oveq2i.mm"
include "sseqtr4i.mm"
include "a1i.mm"
include "simpr.mm"
include "mzpresrename.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem rabdiophlem2
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cM: class M
  let cN: class N
  let va: setvar a
  assume rabdiophlem2.1: |- M = ( N + 1 )

  disjoint N u
  disjoint N t
  disjoint t u
  disjoint M u
  disjoint M t
  disjoint A t
  disjoint N a
  disjoint a u
  disjoint a t
  disjoint M a
  disjoint A a
  assert |- ( ( N e. NN0 /\ ( u e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. ( mzPoly ` ( 1 ... N ) ) ) -> ( t e. ( ZZ ^m ( 1 ... M ) ) |-> [_ ( t |` ( 1 ... N ) ) / u ]_ A ) e. ( mzPoly ` ( 1 ... M ) ) )

  proof
    cN
    cn0
    wcel
    #
    vu
    cz
    c1
    cN
    cfz
    co
    #
    cmap
    co
    #
    cA
    cmpt
    #
    @1
    cmzp
    cfv
    wcel
    #
    wa
    #
    vt
    cz
    c1
    cM
    cfz
    co
    #
    cmap
    co
    #
    vu
    vt
    cv
    #
    @1
    cres
    #
    cA
    csb
    #
    cmpt
    vt
    @7
    @9
    @3
    cfv
    #
    cmpt
    #
    @6
    cmzp
    cfv
    #
    @5
    vt
    @7
    @10
    @11
    @5
    @8
    @7
    wcel
    #
    wa
    #
    @11
    @9
    va
    @2
    vu
    va
    cv
    #
    cA
    csb
    #
    cmpt
    #
    cfv
    #
    @10
    @9
    @3
    @18
    vu
    va
    @2
    cA
    @17
    va
    cA
    nfcv
    vu
    @16
    cA
    nfcsb1v
    vu
    @16
    cA
    csbeq1a
    cbvmpt
    fveq1i
    @15
    @9
    @2
    wcel
    #
    @10
    cz
    wcel
    #
    @19
    @10
    wceq
    @14
    @20
    @5
    @8
    cz
    cM
    cN
    rabdiophlem2.1
    mapfzcons1cl
    adantl
    #
    @15
    @20
    cA
    cz
    wcel
    #
    vu
    @2
    wral
    #
    @21
    @22
    @4
    @24
    @0
    @14
    @4
    @2
    cz
    @3
    wf
    @24
    @3
    @1
    mzpf
    vu
    @2
    cz
    cA
    @3
    @3
    eqid
    fmpt
    sylibr
    ad2antlr
    @23
    @21
    vu
    @9
    @2
    vu
    @10
    cz
    vu
    @9
    cA
    nfcsb1v
    nfel1
    vu
    cv
    @9
    wceq
    cA
    @10
    cz
    vu
    @9
    cA
    csbeq1a
    eleq1d
    rspc
    sylc
    va
    @9
    @17
    @10
    @2
    cz
    @18
    vu
    @16
    @9
    cA
    csbeq1
    @18
    eqid
    fvmptg
    syl2anc
    syl5req
    mpteq2dva
    @5
    @6
    cvv
    wcel
    @1
    @6
    wss
    #
    @4
    @12
    @13
    wcel
    @5
    c1
    cM
    cfz
    ovexd
    @25
    @5
    @1
    c1
    cN
    c1
    caddc
    co
    #
    cfz
    co
    @6
    c1
    cN
    fzssp1
    cM
    @26
    c1
    cfz
    rabdiophlem2.1
    oveq2i
    sseqtr4i
    a1i
    @0
    @4
    simpr
    vt
    @3
    @1
    @6
    mzpresrename
    syl3anc
    eqeltrd
end
