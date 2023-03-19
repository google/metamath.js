include "cn.mm"
include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "cesum.mm"
include "cxad.mm"
include "c1.mm"
include "cseq.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cfz.mm"
include "co.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "wf.mm"
include "wceq.mm"
include "eqid.mm"
include "fmptd.mm"
include "nfmpt1.mm"
include "esumfsup.mm"
include "syl.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "esumeq2dv.mm"
include "wfn.mm"
include "cuz.mm"
include "cz.mm"
include "1z.mm"
include "seqfn.mm"
include "ax-mp.mm"
include "nnuz.mm"
include "fneq2i.mm"
include "mpbir.mm"
include "nfcv.mm"
include "dffn5f.mm"
include "mpbi.mm"
include "a1i.mm"
include "wss.mm"
include "fz1ssnn.mm"
include "sselda.mm"
include "simpll.mm"
include "esumfzf.mm"
include "sylan.mm"
include "eqtr3d.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "3eqtr3d.mm"

theorem esumsup
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let vz: setvar z
  assume esumsup.1: |- ( ph -> B e. ( 0 [,] +oo ) )
  assume esumsup.2: |- ( ( ph /\ k e. NN ) -> A e. ( 0 [,] +oo ) )

  disjoint A n
  disjoint B n
  disjoint k n
  disjoint k ph
  disjoint n ph
  disjoint A z
  disjoint n z
  disjoint B z
  disjoint k z
  disjoint ph z
  assert |- ( ph -> sum* k e. NN A = sup ( ran ( n e. NN |-> sum* k e. ( 1 ... n ) A ) , RR* , < ) )

  proof
    wph
    cn
    vk
    cv
    #
    vk
    cn
    cA
    cmpt
    #
    cfv
    #
    vk
    cesum
    #
    cxad
    @1
    c1
    cseq
    #
    crn
    #
    cxr
    clt
    csup
    #
    cn
    cA
    vk
    cesum
    vn
    cn
    c1
    vn
    cv
    #
    cfz
    co
    #
    cA
    vk
    cesum
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    wph
    cn
    cc0
    cpnf
    cicc
    co
    #
    @1
    wf
    #
    @3
    @6
    wceq
    wph
    vk
    cn
    cA
    @12
    @1
    esumsup.2
    @1
    eqid
    #
    fmptd
    #
    vk
    @1
    vk
    cn
    cA
    nfmpt1
    #
    esumfsup
    syl
    wph
    cn
    @2
    cA
    vk
    wph
    @0
    cn
    wcel
    #
    wa
    @17
    cA
    @12
    wcel
    #
    @2
    cA
    wceq
    #
    wph
    @17
    simpr
    esumsup.2
    vk
    cn
    cA
    @12
    @1
    @14
    fvmpt2
    #
    syl2anc
    esumeq2dv
    wph
    cxr
    @5
    @11
    clt
    wph
    @4
    @10
    wph
    @4
    vn
    cn
    @7
    @4
    cfv
    #
    cmpt
    #
    @10
    @4
    @22
    wceq
    #
    wph
    @4
    cn
    wfn
    #
    @23
    @24
    @4
    c1
    cuz
    cfv
    #
    wfn
    #
    c1
    cz
    wcel
    @26
    1z
    cxad
    @1
    c1
    seqfn
    ax-mp
    cn
    @25
    @4
    nnuz
    fneq2i
    mpbir
    vn
    cn
    @4
    vn
    @4
    nfcv
    dffn5f
    mpbi
    a1i
    wph
    vn
    cn
    @9
    @21
    wph
    @7
    cn
    wcel
    #
    wa
    #
    @8
    @2
    vk
    cesum
    #
    @9
    @21
    @28
    @8
    @2
    cA
    vk
    @28
    @0
    @8
    wcel
    #
    wa
    #
    @17
    @18
    @19
    @28
    @8
    cn
    @0
    @8
    cn
    wss
    @28
    @7
    fz1ssnn
    a1i
    sselda
    #
    @31
    wph
    @17
    @18
    wph
    @27
    @30
    simpll
    @32
    esumsup.2
    syl2anc
    @20
    syl2anc
    esumeq2dv
    wph
    @13
    @27
    @29
    @21
    wceq
    @15
    vk
    @1
    @7
    @16
    esumfzf
    sylan
    eqtr3d
    mpteq2dva
    eqtr4d
    rneqd
    supeq1d
    3eqtr3d
end
