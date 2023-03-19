include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "cn0.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "cdiv.mm"
include "cmpt.mm"
include "cc0.mm"
include "cseq.mm"
include "ce.mm"
include "cli.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cfz.mm"
include "csu.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "sumex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "elfznn0.mm"
include "eqid.mm"
include "eftval.mm"
include "syl.mm"
include "cuz.mm"
include "simpr.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "simpll.mm"
include "eftcl.mm"
include "syl2anc.mm"
include "fsumser.mm"
include "eqtrd.mm"
include "ralrimiva.mm"
include "wfn.mm"
include "wb.mm"
include "fnmpti.mm"
include "cz.mm"
include "0z.mm"
include "seqfn.mm"
include "ax-mp.mm"
include "fneq2i.mm"
include "mpbir.mm"
include "eqfnfv.mm"
include "mp2an.mm"
include "sylibr.mm"
include "efcvg.mm"
include "eqbrtrd.mm"

theorem efcvgfsum
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let vj: setvar j
  assume efcvgfsum.1: |- F = ( n e. NN0 |-> sum_ k e. ( 0 ... n ) ( ( A ^ k ) / ( ! ` k ) ) )

  disjoint k n
  disjoint A k
  disjoint A n
  disjoint j k
  disjoint j n
  disjoint A j
  disjoint F j
  assert |- ( A e. CC -> F ~~> ( exp ` A ) )

  proof
    cA
    cc
    wcel
    #
    cF
    caddc
    vn
    cn0
    cA
    vn
    cv
    #
    cexp
    co
    @1
    cfa
    cfv
    cdiv
    co
    cmpt
    #
    cc0
    cseq
    #
    cA
    ce
    cfv
    cli
    @0
    vj
    cv
    #
    cF
    cfv
    #
    @4
    @3
    cfv
    #
    wceq
    #
    vj
    cn0
    wral
    #
    cF
    @3
    wceq
    #
    @0
    @7
    vj
    cn0
    @0
    @4
    cn0
    wcel
    #
    wa
    #
    @5
    cc0
    @4
    cfz
    co
    #
    cA
    vk
    cv
    #
    cexp
    co
    @13
    cfa
    cfv
    cdiv
    co
    #
    vk
    csu
    #
    @6
    @10
    @5
    @15
    wceq
    @0
    vn
    @4
    cc0
    @1
    cfz
    co
    #
    @14
    vk
    csu
    #
    @15
    cn0
    cF
    @1
    @4
    wceq
    @16
    @12
    @14
    vk
    @1
    @4
    cc0
    cfz
    oveq2
    sumeq1d
    efcvgfsum.1
    @12
    @14
    vk
    sumex
    fvmpt
    adantl
    @11
    @14
    vk
    @2
    cc0
    @4
    @11
    @13
    @12
    wcel
    #
    wa
    #
    @13
    cn0
    wcel
    #
    @13
    @2
    cfv
    @14
    wceq
    @18
    @20
    @11
    @13
    @4
    elfznn0
    adantl
    #
    cA
    vn
    @2
    @13
    @2
    eqid
    #
    eftval
    syl
    @11
    @4
    cn0
    cc0
    cuz
    cfv
    #
    @0
    @10
    simpr
    nn0uz
    syl6eleq
    @19
    @0
    @20
    @14
    cc
    wcel
    @0
    @10
    @18
    simpll
    @21
    cA
    @13
    eftcl
    syl2anc
    fsumser
    eqtrd
    ralrimiva
    cF
    cn0
    wfn
    @3
    cn0
    wfn
    #
    @9
    @8
    wb
    vn
    cn0
    @17
    cF
    @16
    @14
    vk
    sumex
    efcvgfsum.1
    fnmpti
    @24
    @3
    @23
    wfn
    #
    cc0
    cz
    wcel
    @25
    0z
    caddc
    @2
    cc0
    seqfn
    ax-mp
    cn0
    @23
    @3
    nn0uz
    fneq2i
    mpbir
    vj
    cn0
    cF
    @3
    eqfnfv
    mp2an
    sylibr
    cA
    vn
    @2
    @22
    efcvg
    eqbrtrd
end
