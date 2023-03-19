include "cv.mm"
include "cfv.mm"
include "cz.mm"
include "wcel.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cpnf.mm"
include "wceq.mm"
include "uzsup.mm"
include "syl.mm"
include "cmpt.mm"
include "crli.mm"
include "wbr.mm"
include "cli.mm"
include "cvv.mm"
include "wb.mm"
include "climrel.mm"
include "brrelexi.mm"
include "eqid.mm"
include "climmpt.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "cc.mm"
include "wa.mm"
include "recnd.mm"
include "fmptd.mm"
include "rlimclim.mm"
include "mpbird.mm"
include "rlimrecl.mm"

theorem climrecl
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let cG: class G
  let cK: class K
  assume climshft2.1: |- Z = ( ZZ>= ` M )
  assume climshft2.2: |- ( ph -> M e. ZZ )
  assume climrecl.3: |- ( ph -> F ~~> A )
  assume climrecl.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. RR )

  disjoint F k
  disjoint M k
  disjoint k ph
  disjoint Z k
  disjoint A k
  disjoint G k
  disjoint K k
  assert |- ( ph -> A e. RR )

  proof
    wph
    vk
    cZ
    vk
    cv
    #
    cF
    cfv
    #
    cA
    wph
    cM
    cz
    wcel
    #
    cZ
    cxr
    clt
    csup
    cpnf
    wceq
    climshft2.2
    cM
    cZ
    climshft2.1
    uzsup
    syl
    wph
    vk
    cZ
    @1
    cmpt
    #
    cA
    crli
    wbr
    @3
    cA
    cli
    wbr
    #
    wph
    cF
    cA
    cli
    wbr
    #
    @4
    climrecl.3
    wph
    @2
    cF
    cvv
    wcel
    #
    @5
    @4
    wb
    climshft2.2
    wph
    @5
    @6
    climrecl.3
    cF
    cA
    cli
    climrel
    brrelexi
    syl
    cA
    vk
    cF
    @3
    cM
    cvv
    cZ
    climshft2.1
    @3
    eqid
    #
    climmpt
    syl2anc
    mpbid
    wph
    cA
    @3
    cM
    cZ
    climshft2.1
    climshft2.2
    wph
    vk
    cZ
    @1
    cc
    @3
    wph
    @0
    cZ
    wcel
    wa
    @1
    climrecl.4
    recnd
    @7
    fmptd
    rlimclim
    mpbird
    climrecl.4
    rlimrecl
end
