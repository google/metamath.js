include "csu.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cfz.mm"
include "cuz.mm"
include "cfv.mm"
include "eqid.mm"
include "wcel.mm"
include "cz.mm"
include "uzid.mm"
include "syl.mm"
include "peano2uz.mm"
include "syl6eleqr.mm"
include "isumsplit.mm"
include "cv.mm"
include "cc.mm"
include "wceq.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "elfzuz.mm"
include "sylan2.mm"
include "sumeq2dv.mm"
include "wral.mm"
include "wa.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "fsum1.mm"
include "syl2anc.mm"
include "3eqtr2d.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem isum1p
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  assume isum1p.1: |- Z = ( ZZ>= ` M )
  assume isum1p.3: |- ( ph -> M e. ZZ )
  assume isum1p.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume isum1p.5: |- ( ( ph /\ k e. Z ) -> A e. CC )
  assume isum1p.6: |- ( ph -> seq M ( + , F ) e. dom ~~> )

  disjoint F k
  disjoint M k
  disjoint k ph
  disjoint Z k
  assert |- ( ph -> sum_ k e. Z A = ( ( F ` M ) + sum_ k e. ( ZZ>= ` ( M + 1 ) ) A ) )

  proof
    wph
    cZ
    cA
    vk
    csu
    cM
    cM
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    cfz
    co
    #
    cA
    vk
    csu
    #
    @0
    cuz
    cfv
    #
    cA
    vk
    csu
    #
    caddc
    co
    cM
    cF
    cfv
    #
    @5
    caddc
    co
    wph
    cA
    vk
    cF
    cM
    @0
    @4
    cZ
    isum1p.1
    @4
    eqid
    wph
    @0
    cM
    cuz
    cfv
    #
    cZ
    wph
    cM
    @7
    wcel
    #
    @0
    @7
    wcel
    wph
    cM
    cz
    wcel
    #
    @8
    isum1p.3
    cM
    uzid
    syl
    #
    cM
    cM
    peano2uz
    syl
    isum1p.1
    syl6eleqr
    isum1p.4
    isum1p.5
    isum1p.6
    isumsplit
    wph
    @3
    @6
    @5
    caddc
    wph
    @3
    cM
    cM
    cfz
    co
    #
    cA
    vk
    csu
    @11
    vk
    cv
    #
    cF
    cfv
    #
    vk
    csu
    #
    @6
    wph
    @2
    @11
    cA
    vk
    wph
    @1
    cM
    cM
    cfz
    wph
    cM
    cc
    wcel
    c1
    cc
    wcel
    @1
    cM
    wceq
    wph
    cM
    isum1p.3
    zcnd
    ax-1cn
    cM
    c1
    pncan
    sylancl
    oveq2d
    sumeq1d
    wph
    @11
    @13
    cA
    vk
    @12
    @11
    wcel
    #
    wph
    @12
    cZ
    wcel
    #
    @13
    cA
    wceq
    @15
    @12
    @7
    cZ
    @12
    cM
    cM
    elfzuz
    isum1p.1
    syl6eleqr
    isum1p.4
    sylan2
    sumeq2dv
    wph
    @9
    @6
    cc
    wcel
    #
    @14
    @6
    wceq
    isum1p.3
    wph
    cM
    cZ
    wcel
    @13
    cc
    wcel
    #
    vk
    cZ
    wral
    @17
    wph
    cM
    @7
    cZ
    @10
    isum1p.1
    syl6eleqr
    wph
    @18
    vk
    cZ
    wph
    @16
    wa
    @13
    cA
    cc
    isum1p.4
    isum1p.5
    eqeltrd
    ralrimiva
    @18
    @17
    vk
    cM
    cZ
    @12
    cM
    wceq
    @13
    @6
    cc
    @12
    cM
    cF
    fveq2
    #
    eleq1d
    rspcv
    sylc
    @13
    @6
    vk
    cM
    @19
    fsum1
    syl2anc
    3eqtr2d
    oveq1d
    eqtrd
end
