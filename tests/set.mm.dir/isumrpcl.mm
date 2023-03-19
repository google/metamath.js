include "csu.mm"
include "cfv.mm"
include "cuz.mm"
include "wcel.mm"
include "cz.mm"
include "syl6eleq.mm"
include "eluzelz.mm"
include "syl.mm"
include "cv.mm"
include "wceq.mm"
include "wss.mm"
include "uzss.mm"
include "3sstr4g.mm"
include "sselda.mm"
include "syldan.mm"
include "cr.mm"
include "wa.mm"
include "rpred.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "crp.mm"
include "eqeltrd.mm"
include "rpcnd.mm"
include "iserex.mm"
include "mpbid.mm"
include "isumrecl.mm"
include "wral.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "cle.mm"
include "seq1.mm"
include "uzid.mm"
include "syl6eleqr.mm"
include "recnd.mm"
include "isumclim2.mm"
include "sseld.mm"
include "syl6ci.mm"
include "imp.mm"
include "rpge0d.mm"
include "climserle.mm"
include "eqbrtrrd.mm"
include "rpgecld.mm"

theorem isumrpcl
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let cW: class W
  let cZ: class Z
  let vm: setvar m
  assume isumrpcl.1: |- Z = ( ZZ>= ` M )
  assume isumrpcl.2: |- W = ( ZZ>= ` N )
  assume isumrpcl.3: |- ( ph -> N e. Z )
  assume isumrpcl.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume isumrpcl.5: |- ( ( ph /\ k e. Z ) -> A e. RR+ )
  assume isumrpcl.6: |- ( ph -> seq M ( + , F ) e. dom ~~> )

  disjoint F k
  disjoint M k
  disjoint N k
  disjoint k ph
  disjoint W k
  disjoint Z k
  disjoint A m
  disjoint k m
  disjoint F m
  disjoint N m
  disjoint m ph
  disjoint W m
  assert |- ( ph -> sum_ k e. W A e. RR+ )

  proof
    wph
    cW
    cA
    vk
    csu
    #
    cN
    cF
    cfv
    #
    wph
    cA
    vk
    cF
    cN
    cW
    isumrpcl.2
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    cN
    cz
    wcel
    #
    wph
    cN
    cZ
    @2
    isumrpcl.3
    isumrpcl.1
    syl6eleq
    #
    cM
    cN
    eluzelz
    syl
    #
    wph
    vk
    cv
    #
    cW
    wcel
    #
    @7
    cZ
    wcel
    #
    @7
    cF
    cfv
    #
    cA
    wceq
    wph
    cW
    cZ
    @7
    wph
    cN
    cuz
    cfv
    #
    @2
    cW
    cZ
    wph
    @3
    @11
    @2
    wss
    @5
    cM
    cN
    uzss
    syl
    isumrpcl.2
    isumrpcl.1
    3sstr4g
    #
    sselda
    #
    isumrpcl.4
    syldan
    #
    wph
    @8
    @9
    cA
    cr
    wcel
    @13
    wph
    @9
    wa
    #
    cA
    isumrpcl.5
    rpred
    syldan
    #
    wph
    caddc
    cF
    cM
    cseq
    cli
    cdm
    #
    wcel
    caddc
    cF
    cN
    cseq
    #
    @17
    wcel
    isumrpcl.6
    wph
    vk
    cF
    cM
    cN
    cZ
    isumrpcl.1
    isumrpcl.3
    @15
    @10
    @15
    @10
    cA
    crp
    isumrpcl.4
    isumrpcl.5
    eqeltrd
    #
    rpcnd
    iserex
    mpbid
    #
    isumrecl
    wph
    cN
    cZ
    wcel
    @10
    crp
    wcel
    #
    vk
    cZ
    wral
    #
    @1
    crp
    wcel
    #
    isumrpcl.3
    wph
    @21
    vk
    cZ
    @19
    ralrimiva
    #
    @21
    @23
    vk
    cN
    cZ
    @7
    cN
    wceq
    @10
    @1
    crp
    @7
    cN
    cF
    fveq2
    eleq1d
    rspcv
    sylc
    wph
    cN
    @18
    cfv
    #
    @1
    @0
    cle
    wph
    @4
    @25
    @1
    wceq
    @6
    caddc
    cF
    cN
    seq1
    syl
    wph
    @0
    vm
    cF
    cN
    cN
    cW
    isumrpcl.2
    wph
    cN
    @11
    cW
    wph
    @4
    cN
    @11
    wcel
    @6
    cN
    uzid
    syl
    isumrpcl.2
    syl6eleqr
    wph
    cA
    vk
    cF
    cN
    cW
    isumrpcl.2
    @6
    @14
    wph
    @8
    wa
    cA
    @16
    recnd
    @20
    isumclim2
    wph
    vm
    cv
    #
    cW
    wcel
    #
    wa
    #
    @26
    cF
    cfv
    #
    wph
    @27
    @29
    crp
    wcel
    #
    wph
    @27
    @26
    cZ
    wcel
    @22
    @30
    wph
    cW
    cZ
    @26
    @12
    sseld
    @24
    @21
    @30
    vk
    @26
    cZ
    @7
    @26
    wceq
    @10
    @29
    crp
    @7
    @26
    cF
    fveq2
    eleq1d
    rspcv
    syl6ci
    imp
    #
    rpred
    @28
    @29
    @31
    rpge0d
    climserle
    eqbrtrrd
    rpgecld
end
