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
include "crab.mm"
include "cv.mm"
include "csb.mm"
include "wceq.mm"
include "wrex.mm"
include "cdioph.mm"
include "risset.mm"
include "rabbii.mm"
include "a1i.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfeq2.mm"
include "nfrex.mm"
include "csbeq1a.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "cbvrab.mm"
include "syl6eq.mm"
include "caddc.mm"
include "cres.mm"
include "peano2nn0.mm"
include "adantr.mm"
include "cvv.mm"
include "ovex.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "elfz1end.mm"
include "sylib.mm"
include "mzpproj.mm"
include "sylancr.mm"
include "eqid.mm"
include "rabdiophlem2.mm"
include "eqrabdioph.mm"
include "syl3anc.mm"
include "eqeq1.mm"
include "csbeq1.mm"
include "rexrabdioph.mm"
include "syldan.mm"
include "eqeltrd.mm"

theorem elnn0rabdioph
  let vt: setvar t
  let cA: class A
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c

  disjoint N t
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint a t
  disjoint b t
  disjoint c t
  assert |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. ( mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A e. NN0 } e. ( Dioph ` N ) )

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
    cA
    cmpt
    @1
    cmzp
    cfv
    wcel
    #
    wa
    #
    cA
    cn0
    wcel
    #
    vt
    cn0
    @1
    cmap
    co
    #
    crab
    #
    vb
    cv
    #
    vt
    va
    cv
    #
    cA
    csb
    #
    wceq
    #
    vb
    cn0
    wrex
    #
    va
    @5
    crab
    #
    cN
    cdioph
    cfv
    #
    @3
    @6
    @7
    cA
    wceq
    #
    vb
    cn0
    wrex
    #
    vt
    @5
    crab
    #
    @12
    @6
    @16
    wceq
    @3
    @4
    @15
    vt
    @5
    vb
    cA
    cn0
    risset
    rabbii
    a1i
    @15
    @11
    vt
    va
    @5
    vt
    @5
    nfcv
    va
    @5
    nfcv
    @15
    va
    nfv
    @10
    vt
    vb
    cn0
    vt
    cn0
    nfcv
    vt
    @7
    @9
    vt
    @8
    cA
    nfcsb1v
    nfeq2
    nfrex
    vt
    cv
    @8
    wceq
    #
    @14
    @10
    vb
    cn0
    @17
    cA
    @9
    @7
    vt
    @8
    cA
    csbeq1a
    eqeq2d
    rexbidv
    cbvrab
    syl6eq
    @0
    @2
    cN
    c1
    caddc
    co
    #
    vc
    cv
    #
    cfv
    #
    vt
    @19
    @1
    cres
    #
    cA
    csb
    #
    wceq
    #
    vc
    cn0
    c1
    @18
    cfz
    co
    #
    cmap
    co
    crab
    @18
    cdioph
    cfv
    wcel
    #
    @12
    @13
    wcel
    @3
    @18
    cn0
    wcel
    #
    vc
    cz
    @24
    cmap
    co
    #
    @20
    cmpt
    @24
    cmzp
    cfv
    #
    wcel
    #
    vc
    @27
    @22
    cmpt
    @28
    wcel
    @25
    @0
    @26
    @2
    cN
    peano2nn0
    adantr
    @3
    @24
    cvv
    wcel
    @18
    @24
    wcel
    #
    @29
    c1
    @18
    cfz
    ovex
    @0
    @30
    @2
    @0
    @18
    cn
    wcel
    @30
    cN
    nn0p1nn
    @18
    elfz1end
    sylib
    adantr
    vc
    @24
    @18
    mzpproj
    sylancr
    vt
    vc
    cA
    @18
    cN
    @18
    eqid
    #
    rabdiophlem2
    vc
    @20
    @22
    @18
    eqrabdioph
    syl3anc
    @23
    @10
    @20
    @9
    wceq
    vb
    va
    vc
    @18
    cN
    @31
    @7
    @20
    @9
    eqeq1
    @8
    @21
    wceq
    @9
    @22
    @20
    vt
    @8
    @21
    cA
    csbeq1
    eqeq2d
    rexrabdioph
    syldan
    eqeltrd
end
