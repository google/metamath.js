include "caddc.mm"
include "cz.mm"
include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "cfv.mm"
include "cli.mm"
include "csb.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfif.mm"
include "wceq.mm"
include "eleq1.mm"
include "csbeq1a.mm"
include "ifbieq1d.mm"
include "cbvmpt.mm"
include "cc.mm"
include "wral.mm"
include "ralrimiva.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "rspc.mm"
include "mpan9.mm"
include "fsumcvg.mm"
include "cuz.mm"
include "eluzel2.mm"
include "syl.mm"
include "wa.mm"
include "eluzelz.mm"
include "iftrue.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "ex.mm"
include "wn.mm"
include "iffalse.mm"
include "0cn.mm"
include "syl6eqel.mm"
include "pm2.61d1.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anr.mm"
include "eqtr4d.mm"
include "nffvmpt1.mm"
include "nfeq2.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "seqfeq.mm"
include "fveq1d.mm"
include "3brtr4d.mm"

theorem fsumcvg2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  assume fsumsers.1: |- ( ( ph /\ k e. ( ZZ>= ` M ) ) -> ( F ` k ) = if ( k e. A , B , 0 ) )
  assume fsumsers.2: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume fsumsers.3: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume fsumsers.4: |- ( ph -> A C_ ( M ... N ) )

  disjoint A k
  disjoint F k
  disjoint N k
  disjoint k ph
  disjoint M k
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint A m
  disjoint A n
  disjoint B m
  disjoint B n
  disjoint F n
  disjoint N m
  disjoint m ph
  disjoint n ph
  disjoint M m
  disjoint M n
  assert |- ( ph -> seq M ( + , F ) ~~> ( seq M ( + , F ) ` N ) )

  proof
    wph
    caddc
    vk
    cz
    vk
    cv
    #
    cA
    wcel
    #
    cB
    cc0
    cif
    #
    cmpt
    #
    cM
    cseq
    #
    cN
    @4
    cfv
    caddc
    cF
    cM
    cseq
    #
    cN
    @5
    cfv
    cli
    wph
    cA
    vk
    vm
    cv
    #
    cB
    csb
    #
    vm
    @3
    cM
    cN
    vk
    vm
    cz
    @2
    @6
    cA
    wcel
    #
    @7
    cc0
    cif
    vm
    @2
    nfcv
    @8
    vk
    @7
    cc0
    @8
    vk
    nfv
    vk
    @6
    cB
    nfcsb1v
    #
    vk
    cc0
    nfcv
    nfif
    @0
    @6
    wceq
    #
    @1
    @8
    cB
    @7
    cc0
    @0
    @6
    cA
    eleq1
    vk
    @6
    cB
    csbeq1a
    #
    ifbieq1d
    cbvmpt
    wph
    cB
    cc
    wcel
    #
    vk
    cA
    wral
    @8
    @7
    cc
    wcel
    #
    wph
    @12
    vk
    cA
    fsumsers.3
    ralrimiva
    @12
    @13
    vk
    @6
    cA
    vk
    @7
    cc
    @9
    nfel1
    @10
    cB
    @7
    cc
    @11
    eleq1d
    rspc
    mpan9
    fsumsers.2
    fsumsers.4
    fsumcvg
    wph
    caddc
    vn
    cF
    @3
    cM
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    cM
    cz
    wcel
    fsumsers.2
    cM
    cN
    eluzel2
    syl
    wph
    @0
    cF
    cfv
    #
    @0
    @3
    cfv
    #
    wceq
    #
    vk
    @14
    wral
    vn
    cv
    #
    @14
    wcel
    @18
    cF
    cfv
    #
    @18
    @3
    cfv
    #
    wceq
    #
    wph
    @17
    vk
    @14
    wph
    @0
    @14
    wcel
    #
    wa
    @15
    @2
    @16
    fsumsers.1
    @22
    @0
    cz
    wcel
    @2
    cc
    wcel
    #
    @16
    @2
    wceq
    wph
    cM
    @0
    eluzelz
    wph
    @1
    @23
    wph
    @1
    @23
    wph
    @1
    wa
    @2
    cB
    cc
    @1
    @2
    cB
    wceq
    wph
    @1
    cB
    cc0
    iftrue
    adantl
    fsumsers.3
    eqeltrd
    ex
    @1
    wn
    @2
    cc0
    cc
    @1
    cB
    cc0
    iffalse
    0cn
    syl6eqel
    pm2.61d1
    vk
    cz
    @2
    cc
    @3
    @3
    eqid
    fvmpt2
    syl2anr
    eqtr4d
    ralrimiva
    @17
    @21
    vk
    @18
    @14
    vk
    @19
    @20
    vk
    cz
    @2
    @18
    nffvmpt1
    nfeq2
    @0
    @18
    wceq
    @15
    @19
    @16
    @20
    @0
    @18
    cF
    fveq2
    @0
    @18
    @3
    fveq2
    eqeq12d
    rspc
    mpan9
    seqfeq
    #
    wph
    cN
    @5
    @4
    @24
    fveq1d
    3brtr4d
end
