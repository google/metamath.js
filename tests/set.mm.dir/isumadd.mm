include "caddc.mm"
include "co.mm"
include "csu.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "eqtrd.mm"
include "addcld.mm"
include "cseq.mm"
include "cvv.mm"
include "isumclim2.mm"
include "seqex.mm"
include "a1i.mm"
include "cc.mm"
include "eqeltrd.mm"
include "serf.mm"
include "ffvelrnda.mm"
include "cuz.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "cfz.mm"
include "simpll.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "syl2anc.mm"
include "syl.mm"
include "seradd.mm"
include "climadd.mm"
include "isumclim.mm"

theorem isumadd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vm: setvar m
  assume isumadd.1: |- Z = ( ZZ>= ` M )
  assume isumadd.2: |- ( ph -> M e. ZZ )
  assume isumadd.3: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume isumadd.4: |- ( ( ph /\ k e. Z ) -> A e. CC )
  assume isumadd.5: |- ( ( ph /\ k e. Z ) -> ( G ` k ) = B )
  assume isumadd.6: |- ( ( ph /\ k e. Z ) -> B e. CC )
  assume isumadd.7: |- ( ph -> seq M ( + , F ) e. dom ~~> )
  assume isumadd.8: |- ( ph -> seq M ( + , G ) e. dom ~~> )

  disjoint F k
  disjoint G k
  disjoint M k
  disjoint k ph
  disjoint Z k
  disjoint j k
  disjoint j m
  disjoint F j
  disjoint k m
  disjoint F m
  disjoint G j
  disjoint G m
  disjoint M j
  disjoint j ph
  disjoint Z j
  disjoint Z m
  disjoint A j
  disjoint B j
  assert |- ( ph -> sum_ k e. Z ( A + B ) = ( sum_ k e. Z A + sum_ k e. Z B ) )

  proof
    wph
    cA
    cB
    caddc
    co
    #
    cZ
    cA
    vk
    csu
    #
    cZ
    cB
    vk
    csu
    #
    caddc
    co
    vk
    vm
    cZ
    vm
    cv
    #
    cF
    cfv
    #
    @3
    cG
    cfv
    #
    caddc
    co
    #
    cmpt
    #
    cM
    cZ
    isumadd.1
    isumadd.2
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @8
    @7
    cfv
    #
    @8
    cF
    cfv
    #
    @8
    cG
    cfv
    #
    caddc
    co
    #
    @0
    @9
    @11
    @14
    wceq
    #
    wph
    vm
    @8
    @6
    @14
    cZ
    @7
    @3
    @8
    wceq
    @4
    @12
    @5
    @13
    caddc
    @3
    @8
    cF
    fveq2
    @3
    @8
    cG
    fveq2
    oveq12d
    @7
    eqid
    @12
    @13
    caddc
    ovex
    fvmpt
    #
    adantl
    @10
    @12
    cA
    @13
    cB
    caddc
    isumadd.3
    isumadd.5
    oveq12d
    eqtrd
    @10
    cA
    cB
    isumadd.4
    isumadd.6
    addcld
    wph
    @1
    @2
    vj
    caddc
    cF
    cM
    cseq
    #
    caddc
    cG
    cM
    cseq
    #
    caddc
    @7
    cM
    cseq
    #
    cM
    cvv
    cZ
    isumadd.1
    isumadd.2
    wph
    cA
    vk
    cF
    cM
    cZ
    isumadd.1
    isumadd.2
    isumadd.3
    isumadd.4
    isumadd.7
    isumclim2
    @19
    cvv
    wcel
    wph
    caddc
    @7
    cM
    seqex
    a1i
    wph
    cB
    vk
    cG
    cM
    cZ
    isumadd.1
    isumadd.2
    isumadd.5
    isumadd.6
    isumadd.8
    isumclim2
    wph
    cZ
    cc
    vj
    cv
    #
    @17
    wph
    vk
    cF
    cM
    cZ
    isumadd.1
    isumadd.2
    @10
    @12
    cA
    cc
    isumadd.3
    isumadd.4
    eqeltrd
    #
    serf
    ffvelrnda
    wph
    cZ
    cc
    @20
    @18
    wph
    vk
    cG
    cM
    cZ
    isumadd.1
    isumadd.2
    @10
    @13
    cB
    cc
    isumadd.5
    isumadd.6
    eqeltrd
    #
    serf
    ffvelrnda
    wph
    @20
    cZ
    wcel
    #
    wa
    #
    vk
    cF
    cG
    @7
    cM
    @20
    @24
    @20
    cZ
    cM
    cuz
    cfv
    #
    wph
    @23
    simpr
    isumadd.1
    syl6eleq
    @24
    @8
    cM
    @20
    cfz
    co
    wcel
    #
    wa
    #
    wph
    @9
    @12
    cc
    wcel
    wph
    @23
    @26
    simpll
    #
    @26
    @9
    @24
    @26
    @8
    @25
    cZ
    @8
    cM
    @20
    elfzuz
    isumadd.1
    syl6eleqr
    adantl
    #
    @21
    syl2anc
    @27
    wph
    @9
    @13
    cc
    wcel
    @28
    @29
    @22
    syl2anc
    @27
    @9
    @15
    @29
    @16
    syl
    seradd
    climadd
    isumclim
end
