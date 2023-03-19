include "cneg.mm"
include "cshi.mm"
include "co.mm"
include "cli.mm"
include "wbr.mm"
include "cvv.mm"
include "ovexd.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "caddc.mm"
include "cid.mm"
include "cc.mm"
include "wceq.mm"
include "zcnd.mm"
include "cz.mm"
include "cuz.mm"
include "eluzelz.mm"
include "eleq2s.mm"
include "fvex.mm"
include "shftval4.mm"
include "syl2an.mm"
include "fvi.mm"
include "syl.mm"
include "adantr.mm"
include "oveq1d.mm"
include "fveq1d.mm"
include "addcom.mm"
include "fveq12d.mm"
include "3eqtr3d.mm"
include "eqtrd.mm"
include "climeq.mm"
include "wb.mm"
include "znegcld.mm"
include "climshft.mm"
include "syl2anc.mm"
include "bitr3d.mm"

theorem climshft2
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cK: class K
  let cM: class M
  let cW: class W
  let cX: class X
  let cZ: class Z
  assume climshft2.1: |- Z = ( ZZ>= ` M )
  assume climshft2.2: |- ( ph -> M e. ZZ )
  assume climshft2.3: |- ( ph -> K e. ZZ )
  assume climshft2.5: |- ( ph -> F e. W )
  assume climshft2.6: |- ( ph -> G e. X )
  assume climshft2.7: |- ( ( ph /\ k e. Z ) -> ( G ` ( k + K ) ) = ( F ` k ) )

  disjoint F k
  disjoint G k
  disjoint K k
  disjoint M k
  disjoint k ph
  disjoint Z k
  disjoint A k
  assert |- ( ph -> ( F ~~> A <-> G ~~> A ) )

  proof
    wph
    cG
    cK
    cneg
    #
    cshi
    co
    #
    cA
    cli
    wbr
    #
    cF
    cA
    cli
    wbr
    cG
    cA
    cli
    wbr
    #
    wph
    cA
    vk
    @1
    cF
    cM
    cvv
    cW
    cZ
    climshft2.1
    wph
    cG
    @0
    cshi
    ovexd
    climshft2.5
    climshft2.2
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @4
    @1
    cfv
    #
    @4
    cK
    caddc
    co
    #
    cG
    cfv
    #
    @4
    cF
    cfv
    @6
    @4
    cG
    cid
    cfv
    #
    @0
    cshi
    co
    #
    cfv
    #
    cK
    @4
    caddc
    co
    #
    @10
    cfv
    #
    @7
    @9
    wph
    cK
    cc
    wcel
    #
    @4
    cc
    wcel
    #
    @12
    @14
    wceq
    @5
    wph
    cK
    climshft2.3
    zcnd
    #
    @5
    @4
    @4
    cz
    wcel
    @4
    cM
    cuz
    cfv
    cZ
    cM
    @4
    eluzelz
    climshft2.1
    eleq2s
    zcnd
    #
    cK
    @4
    @10
    cG
    cid
    fvex
    shftval4
    syl2an
    @6
    @4
    @11
    @1
    @6
    @10
    cG
    @0
    cshi
    wph
    @10
    cG
    wceq
    #
    @5
    wph
    cG
    cX
    wcel
    #
    @19
    climshft2.6
    cG
    cX
    fvi
    syl
    adantr
    #
    oveq1d
    fveq1d
    @6
    @13
    @8
    @10
    cG
    @21
    wph
    @15
    @16
    @13
    @8
    wceq
    @5
    @17
    @18
    cK
    @4
    addcom
    syl2an
    fveq12d
    3eqtr3d
    climshft2.7
    eqtrd
    climeq
    wph
    @0
    cz
    wcel
    @20
    @2
    @3
    wb
    wph
    cK
    climshft2.3
    znegcld
    climshft2.6
    cA
    cG
    @0
    cX
    climshft
    syl2anc
    bitr3d
end
