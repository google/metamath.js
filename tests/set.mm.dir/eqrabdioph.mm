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
include "w3a.mm"
include "wceq.mm"
include "crab.mm"
include "cmin.mm"
include "cc0.mm"
include "cdioph.mm"
include "wa.mm"
include "wb.mm"
include "wral.mm"
include "nfmpt1.mm"
include "nfel1.mm"
include "nfan.mm"
include "cv.mm"
include "wf.mm"
include "mzpf.mm"
include "ad2antrr.mm"
include "cvv.mm"
include "wss.mm"
include "zex.mm"
include "nn0ssz.mm"
include "mapss.mm"
include "mp2an.mm"
include "sseli.mm"
include "adantl.mm"
include "mptfcl.mm"
include "sylc.mm"
include "zcnd.mm"
include "ad2antlr.mm"
include "subeq0ad.mm"
include "bicomd.mm"
include "ex.mm"
include "ralrimi.mm"
include "rabbi.mm"
include "sylib.mm"
include "3adant1.mm"
include "simp1.mm"
include "mzpsubmpt.mm"
include "eq0rabdioph.mm"
include "syl2anc.mm"
include "eqeltrd.mm"

theorem eqrabdioph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cN: class N
  let va: setvar a
  let vb: setvar b

  disjoint N t
  disjoint N a
  disjoint N b
  disjoint a t
  disjoint b t
  disjoint a b
  disjoint A a
  disjoint A b
  disjoint B a
  disjoint B b
  assert |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. ( mzPoly ` ( 1 ... N ) ) /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> B ) e. ( mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A = B } e. ( Dioph ` N ) )

  proof
    cN
    cn0
    wcel
    #
    vt
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
    #
    wcel
    #
    vt
    @2
    cB
    cmpt
    #
    @4
    wcel
    #
    w3a
    #
    cA
    cB
    wceq
    #
    vt
    cn0
    @1
    cmap
    co
    #
    crab
    #
    cA
    cB
    cmin
    co
    #
    cc0
    wceq
    #
    vt
    @10
    crab
    #
    cN
    cdioph
    cfv
    #
    @5
    @7
    @11
    @14
    wceq
    #
    @0
    @5
    @7
    wa
    #
    @9
    @13
    wb
    #
    vt
    @10
    wral
    @16
    @17
    @18
    vt
    @10
    @5
    @7
    vt
    vt
    @3
    @4
    vt
    @2
    cA
    nfmpt1
    nfel1
    vt
    @6
    @4
    vt
    @2
    cB
    nfmpt1
    nfel1
    nfan
    @17
    vt
    cv
    #
    @10
    wcel
    #
    @18
    @17
    @20
    wa
    #
    @13
    @9
    @21
    cA
    cB
    @21
    cA
    @21
    @2
    cz
    @3
    wf
    #
    @19
    @2
    wcel
    #
    cA
    cz
    wcel
    @5
    @22
    @7
    @20
    @3
    @1
    mzpf
    ad2antrr
    @20
    @23
    @17
    @10
    @2
    @19
    cz
    cvv
    wcel
    cn0
    cz
    wss
    @10
    @2
    wss
    zex
    nn0ssz
    cn0
    cz
    @1
    cvv
    mapss
    mp2an
    sseli
    adantl
    #
    vt
    @2
    cA
    cz
    mptfcl
    sylc
    zcnd
    @21
    cB
    @21
    @2
    cz
    @6
    wf
    #
    @23
    cB
    cz
    wcel
    @7
    @25
    @5
    @20
    @6
    @1
    mzpf
    ad2antlr
    @24
    vt
    @2
    cB
    cz
    mptfcl
    sylc
    zcnd
    subeq0ad
    bicomd
    ex
    ralrimi
    @9
    @13
    vt
    @10
    rabbi
    sylib
    3adant1
    @8
    @0
    vt
    @2
    @12
    cmpt
    @4
    wcel
    #
    @14
    @15
    wcel
    @0
    @5
    @7
    simp1
    @5
    @7
    @26
    @0
    vt
    cA
    cB
    @1
    mzpsubmpt
    3adant1
    vt
    @12
    cN
    eq0rabdioph
    syl2anc
    eqeltrd
end
