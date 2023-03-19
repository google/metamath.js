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
include "cc0.mm"
include "wceq.mm"
include "crab.mm"
include "cv.mm"
include "cres.mm"
include "wrex.mm"
include "cab.mm"
include "cdioph.mm"
include "wb.mm"
include "wral.mm"
include "nfv.mm"
include "nfmpt1.mm"
include "nfel1.mm"
include "nfan.mm"
include "cvv.mm"
include "wss.mm"
include "zex.mm"
include "nn0ssz.mm"
include "mapss.mm"
include "mp2an.mm"
include "sseli.mm"
include "adantl.mm"
include "wf.mm"
include "mzpf.mm"
include "mptfcl.mm"
include "imp.mm"
include "syl2an.mm"
include "adantll.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "eqeq1d.mm"
include "ex.mm"
include "ralrimi.mm"
include "rabbi.mm"
include "sylib.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nfeq1.mm"
include "fveq2.mm"
include "cbvrab.mm"
include "syl6eq.mm"
include "df-rab.mm"
include "wfn.mm"
include "elmapi.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "eqeq2d.mm"
include "equcom.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "rexbiia.mm"
include "ceqsrexbv.mm"
include "bitr2i.mm"
include "abbii.mm"
include "cuz.mm"
include "simpl.mm"
include "nn0z.mm"
include "uzid.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "eldioph.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem eq0rabdioph
  let vt: setvar t
  let cA: class A
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let cB: class B

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
  assert |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. ( mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A = 0 } e. ( Dioph ` N ) )

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
    wa
    #
    cA
    cc0
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
    va
    cv
    #
    vb
    cv
    #
    @1
    cres
    #
    wceq
    #
    @11
    @3
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vb
    @8
    wrex
    #
    va
    cab
    #
    cN
    cdioph
    cfv
    #
    @6
    @9
    @10
    @8
    wcel
    @10
    @3
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    va
    cab
    #
    @18
    @6
    @9
    @21
    va
    @8
    crab
    #
    @23
    @6
    @9
    vt
    cv
    #
    @3
    cfv
    #
    cc0
    wceq
    #
    vt
    @8
    crab
    #
    @24
    @6
    @7
    @27
    wb
    #
    vt
    @8
    wral
    @9
    @28
    wceq
    @6
    @29
    vt
    @8
    @0
    @5
    vt
    @0
    vt
    nfv
    vt
    @3
    @4
    vt
    @2
    cA
    nfmpt1
    nfel1
    nfan
    @6
    @25
    @8
    wcel
    #
    @29
    @6
    @30
    wa
    #
    cA
    @26
    cc0
    @31
    @26
    cA
    @31
    @25
    @2
    wcel
    #
    cA
    cz
    wcel
    #
    @26
    cA
    wceq
    @30
    @32
    @6
    @8
    @2
    @25
    cz
    cvv
    wcel
    cn0
    cz
    wss
    @8
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
    #
    adantl
    @5
    @30
    @33
    @0
    @5
    @2
    cz
    @3
    wf
    #
    @32
    @33
    @30
    @3
    @1
    mzpf
    @34
    @35
    @32
    @33
    vt
    @2
    cA
    cz
    mptfcl
    imp
    syl2an
    adantll
    vt
    @2
    cA
    cz
    @3
    @3
    eqid
    fvmpt2
    syl2anc
    eqcomd
    eqeq1d
    ex
    ralrimi
    @7
    @27
    vt
    @8
    rabbi
    sylib
    @27
    @21
    vt
    va
    @8
    vt
    @8
    nfcv
    va
    @8
    nfcv
    @27
    va
    nfv
    vt
    @20
    cc0
    vt
    @2
    cA
    @10
    nffvmpt1
    nfeq1
    @25
    @10
    wceq
    @26
    @20
    cc0
    @25
    @10
    @3
    fveq2
    eqeq1d
    cbvrab
    syl6eq
    @21
    va
    @8
    df-rab
    syl6eq
    @22
    @17
    va
    @17
    @11
    @10
    wceq
    #
    @15
    wa
    #
    vb
    @8
    wrex
    @22
    @16
    @37
    vb
    @8
    @11
    @8
    wcel
    #
    @13
    @36
    @15
    @38
    @13
    @10
    @11
    wceq
    @36
    @38
    @12
    @11
    @10
    @38
    @1
    cn0
    @11
    wf
    @11
    @1
    wfn
    @12
    @11
    wceq
    @11
    cn0
    @1
    elmapi
    @1
    cn0
    @11
    ffn
    @1
    @11
    fnresdm
    3syl
    eqeq2d
    va
    vb
    equcom
    syl6bb
    anbi1d
    rexbiia
    @15
    @21
    vb
    @10
    @8
    @36
    @14
    @20
    cc0
    @11
    @10
    @3
    fveq2
    eqeq1d
    ceqsrexbv
    bitr2i
    abbii
    syl6eq
    @6
    @0
    cN
    cN
    cuz
    cfv
    wcel
    #
    @5
    @18
    @19
    wcel
    @0
    @5
    simpl
    @0
    @39
    @5
    @0
    cN
    cz
    wcel
    @39
    cN
    nn0z
    cN
    uzid
    syl
    adantr
    @0
    @5
    simpr
    vb
    va
    @3
    cN
    cN
    eldioph
    syl3anc
    eqeltrd
end
