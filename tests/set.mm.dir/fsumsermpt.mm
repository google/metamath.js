include "cv.mm"
include "cfz.mm"
include "co.mm"
include "csu.mm"
include "cc.mm"
include "wcel.mm"
include "wral.mm"
include "wfn.mm"
include "fzfid.mm"
include "wa.mm"
include "simpl.mm"
include "cuz.mm"
include "cfv.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "adantl.mm"
include "syl2anc.mm"
include "fsumcl.mm"
include "adantr.mm"
include "ralrimiva.mm"
include "cmpt.mm"
include "wceq.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "fnmpt.mm"
include "syl.mm"
include "caddc.mm"
include "cseq.mm"
include "wf.mm"
include "csb.mm"
include "simpr.mm"
include "wi.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfcsb1.mm"
include "nfel1.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "eqid.mm"
include "fvmptf.mm"
include "eqeltrd.mm"
include "addcl.mm"
include "seqf.mm"
include "ffn.mm"
include "a1i.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "fvmpt2.mm"
include "cbvsum.mm"
include "eqtrd.mm"
include "adantlr.mm"
include "id.mm"
include "syl6eleq.mm"
include "fsumser.mm"
include "fveq1i.mm"
include "eqcomi.mm"
include "3eqtrd.mm"
include "eqfnfvd.mm"

theorem fsumsermpt
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vm: setvar m
  let vx: setvar x
  assume fsumsermpt.m: |- ( ph -> M e. ZZ )
  assume fsumsermpt.z: |- Z = ( ZZ>= ` M )
  assume fsumsermpt.a: |- ( ( ph /\ k e. Z ) -> A e. CC )
  assume fsumsermpt.f: |- F = ( n e. Z |-> sum_ k e. ( M ... n ) A )
  assume fsumsermpt.g: |- G = seq M ( + , ( k e. Z |-> A ) )

  disjoint A n
  disjoint M k
  disjoint M n
  disjoint k n
  disjoint Z k
  disjoint Z n
  disjoint k ph
  disjoint A j
  disjoint A m
  disjoint j m
  disjoint m n
  disjoint A x
  disjoint j x
  disjoint F m
  disjoint G m
  disjoint M j
  disjoint M m
  disjoint j k
  disjoint k m
  disjoint M x
  disjoint k x
  disjoint Z j
  disjoint Z m
  disjoint Z x
  disjoint j ph
  disjoint m ph
  disjoint ph x
  assert |- ( ph -> F = G )

  proof
    wph
    vm
    cZ
    cF
    cG
    wph
    cM
    vm
    cv
    #
    cfz
    co
    #
    cA
    vk
    csu
    #
    cc
    wcel
    #
    vm
    cZ
    wral
    cF
    cZ
    wfn
    wph
    @3
    vm
    cZ
    wph
    @3
    @0
    cZ
    wcel
    #
    wph
    @1
    cA
    vk
    wph
    cM
    @0
    fzfid
    wph
    vk
    cv
    #
    @1
    wcel
    #
    wa
    wph
    @5
    cZ
    wcel
    #
    cA
    cc
    wcel
    #
    wph
    @6
    simpl
    @6
    @7
    wph
    @6
    @5
    cM
    cuz
    cfv
    #
    cZ
    @5
    cM
    @0
    elfzuz
    fsumsermpt.z
    syl6eleqr
    adantl
    fsumsermpt.a
    syl2anc
    fsumcl
    adantr
    #
    ralrimiva
    vm
    cZ
    @2
    cF
    cc
    cF
    vn
    cZ
    cM
    vn
    cv
    #
    cfz
    co
    #
    cA
    vk
    csu
    #
    cmpt
    vm
    cZ
    @2
    cmpt
    fsumsermpt.f
    vn
    vm
    cZ
    @13
    @2
    @11
    @0
    wceq
    @12
    @1
    cA
    vk
    @11
    @0
    cM
    cfz
    oveq2
    sumeq1d
    cbvmptv
    eqtri
    #
    fnmpt
    syl
    wph
    cG
    cZ
    wfn
    caddc
    vk
    cZ
    cA
    cmpt
    #
    cM
    cseq
    #
    cZ
    wfn
    #
    wph
    cZ
    cc
    @16
    wf
    @17
    wph
    vj
    vx
    caddc
    cc
    @15
    cM
    cZ
    fsumsermpt.z
    fsumsermpt.m
    wph
    vj
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @18
    @15
    cfv
    #
    vk
    @18
    cA
    csb
    #
    cc
    @20
    @19
    @22
    cc
    wcel
    #
    @21
    @22
    wceq
    #
    wph
    @19
    simpr
    wph
    @7
    wa
    #
    @8
    wi
    @20
    @23
    wi
    vk
    vj
    @20
    @23
    vk
    @20
    vk
    nfv
    vk
    @22
    cc
    vk
    @18
    cA
    vk
    @18
    nfcv
    #
    nfcsb1
    #
    nfel1
    nfim
    @5
    @18
    wceq
    #
    @25
    @20
    @8
    @23
    @28
    @7
    @19
    wph
    @5
    @18
    cZ
    eleq1
    anbi2d
    @28
    cA
    @22
    cc
    vk
    @18
    cA
    csbeq1a
    #
    eleq1d
    imbi12d
    fsumsermpt.a
    chvar
    #
    vk
    @18
    cA
    @22
    cZ
    @15
    cc
    @26
    @27
    @29
    @15
    eqid
    fvmptf
    syl2anc
    #
    @30
    eqeltrd
    @18
    cc
    wcel
    vx
    cv
    #
    cc
    wcel
    wa
    @18
    @32
    caddc
    co
    cc
    wcel
    wph
    @18
    @32
    addcl
    adantl
    seqf
    cZ
    cc
    @16
    ffn
    syl
    wph
    cZ
    cG
    @16
    cG
    @16
    wceq
    wph
    fsumsermpt.g
    a1i
    fneq1d
    mpbird
    wph
    @4
    wa
    #
    @0
    cF
    cfv
    #
    @1
    @22
    vj
    csu
    #
    @0
    @16
    cfv
    #
    @0
    cG
    cfv
    #
    @33
    @34
    @2
    @35
    @33
    @4
    @3
    @34
    @2
    wceq
    wph
    @4
    simpr
    @10
    vm
    cZ
    @2
    cc
    cF
    @14
    fvmpt2
    syl2anc
    @2
    @35
    wceq
    @33
    @1
    cA
    @22
    vk
    vj
    @29
    vj
    @1
    nfcv
    vk
    @1
    nfcv
    vj
    cA
    nfcv
    @27
    cbvsum
    a1i
    eqtrd
    @33
    @22
    vj
    @15
    cM
    @0
    wph
    @18
    @1
    wcel
    #
    @24
    @4
    wph
    @38
    wa
    #
    wph
    @19
    @24
    wph
    @38
    simpl
    #
    @38
    @19
    wph
    @38
    @18
    @9
    cZ
    @18
    cM
    @0
    elfzuz
    fsumsermpt.z
    syl6eleqr
    adantl
    #
    @31
    syl2anc
    adantlr
    @4
    @0
    @9
    wcel
    wph
    @4
    @0
    cZ
    @9
    @4
    id
    fsumsermpt.z
    syl6eleq
    adantl
    wph
    @38
    @23
    @4
    @39
    wph
    @19
    @23
    @40
    @41
    @30
    syl2anc
    adantlr
    fsumser
    @36
    @37
    wceq
    @33
    @37
    @36
    @0
    cG
    @16
    fsumsermpt.g
    fveq1i
    eqcomi
    a1i
    3eqtrd
    eqfnfvd
end
